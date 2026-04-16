// encoding.h -- Bounded-synthesis encodings and DIMACS serialisation
//
// This file contains:
//   1. Specification struct         -- parsed BoSy JSON spec
//   2. Utility functions            -- numBitsNeeded, binaryFrom
//   3. Bit-vector comparison        -- bvGreater / bvGreaterOrEqual
//   4. TseitinEncoder               -- formula tree -> CNF clauses
//   5. QBFProblem  + toQDIMACS()    -- 3-block QBF (∃∀∃) serialisation
//   6. DQBFProblem + toDQDIMACS()   -- DQBF serialisation with per-variable
//                                      dependency sets
//   7. buildInputSymbolicQBF()      -- InputSymbolic encoding (QBF)
//   8. buildStateSymbolicDQBF()     -- StateSymbolic encoding (DQBF)
//   9. buildSymbolicDQBF()          -- Fully Symbolic encoding (DQBF)
//
// Corresponds to:
//   Sources/BoundedSynthesis/InputSymbolicEncoding.swift
//   Sources/BoundedSynthesis/StateSymbolicEncoding.swift
//   Sources/BoundedSynthesis/SymbolicEncoding.swift
//   Sources/Logic/Transformer.swift   (QDIMACSVisitor, DQDIMACSVisitor)
//   Sources/Utils/Function.swift      (numBitsNeeded, binaryFrom)

#pragma once
#include "formula.h"
#include "automaton.h"
#include <map>
#include <vector>
#include <string>
#include <sstream>
#include <cassert>

// ===========================================================================
// Specification  (mirrors SynthesisSpecification in BoSy)
// ===========================================================================

struct Specification {
    enum Semantics { Mealy, Moore } semantics = Mealy;
    std::vector<std::string> inputs;
    std::vector<std::string> outputs;
    std::vector<std::string> assumptions;  // LTL strings
    std::vector<std::string> guarantees;   // LTL strings
};

// ===========================================================================
// Utilities
// ===========================================================================

// Minimum number of bits to represent values in [0, x).
// Matches BoSy's numBitsNeeded() in Sources/Utils/Function.swift.
inline int numBitsNeeded(int x) {
    if (x <= 1) return 1;
    if (x == 2) return 1;
    if (x % 2 != 0) return 1 + numBitsNeeded(x - 1);
    return 1 + numBitsNeeded(x / 2);
}

// Return the binary representation of n as a string of length `bits`,
// MSB first (index 0 = most significant bit).
inline std::string binaryFrom(int n, int bits) {
    std::string s;
    for (int i = bits - 1; i >= 0; --i)
        s += ((n >> i) & 1) ? '1' : '0';
    return s;
}

// ===========================================================================
// Bit-vector comparison  (MSB-first)
//
// These build propositional formulas representing lexicographic comparison
// of two bit-vectors a and b (index 0 = MSB).  They implement the same
// recursive structure as BoSy's `order()` function in Logic.swift.
//
// The bounded-synthesis ranking function uses an *increasing* counter:
//   - Rejecting target  in same SCC:  lambdaSharp' >  lambdaSharp
//   - Non-rejecting target in same SCC: lambdaSharp' >= lambdaSharp
// Because the counter is bounded, rejecting states can only be visited
// finitely often.
// ===========================================================================

inline Fml bvGreater(const std::vector<Fml>& a, const std::vector<Fml>& b) {
    assert(a.size() == b.size() && !a.empty());
    Fml gt = fAnd(a[0], fNot(b[0]));   // MSB: a=1, b=0  =>  a > b
    Fml eq = fIff(a[0], b[0]);          // MSBs equal => compare rest
    if (a.size() == 1) return gt;
    std::vector<Fml> ra(a.begin()+1, a.end()), rb(b.begin()+1, b.end());
    return fOr(gt, fAnd(eq, bvGreater(ra, rb)));
}

inline Fml bvGreaterOrEqual(const std::vector<Fml>& a, const std::vector<Fml>& b) {
    assert(a.size() == b.size() && !a.empty());
    Fml gt = fAnd(a[0], fNot(b[0]));
    Fml eq = fIff(a[0], b[0]);
    if (a.size() == 1) return fOr(gt, eq);  // single bit: a >= b
    std::vector<Fml> ra(a.begin()+1, a.end()), rb(b.begin()+1, b.end());
    return fOr(gt, fAnd(eq, bvGreaterOrEqual(ra, rb)));
}

// ===========================================================================
// Tseitin encoder
//
// Converts an arbitrary propositional formula tree (Fml) into an
// equisatisfiable set of CNF clauses by introducing auxiliary variables
// for each sub-formula.  Each node in the DAG is visited at most once
// (pointer-based memoisation via cache_).
//
// Usage:
//   1. Optionally call reserveAtom() to pre-assign IDs to known atoms
//      (this controls which variable IDs fall into which quantifier
//      block in the final QDIMACS/DQDIMACS output).
//   2. Call encode(root) to get the literal representing the root.
//   3. Add a unit clause {topLit} to assert the formula.
//   4. Variables with IDs > reserved belong to Tseitin auxiliaries.
//
// Corresponds to DIMACSVisitor / QDIMACSVisitor in Transformer.swift.
// ===========================================================================

class TseitinEncoder {
    std::map<std::string, int> atomIds_;      // atom name -> DIMACS var id
    std::map<const Formula*, int> cache_;      // DAG node -> literal (memo)
    int nextId_ = 1;
    std::vector<std::vector<int>> clauses_;

public:
    int allocId() { return nextId_++; }

    // Get (or create) the DIMACS variable ID for a named atom.
    int getOrAllocAtom(const std::string& name) {
        auto [it, ok] = atomIds_.try_emplace(name, nextId_);
        if (ok) nextId_++;
        return it->second;
    }

    // Pre-assign an ID without encoding anything.
    void reserveAtom(const std::string& name) { getOrAllocAtom(name); }

    int atomId(const std::string& name) const { return atomIds_.at(name); }

    bool hasAtom(const std::string& name) const {
        return atomIds_.count(name) > 0;
    }

    int numVars() const { return nextId_ - 1; }
    const std::vector<std::vector<int>>& clauses() const { return clauses_; }
    const std::map<std::string, int>& atomMap() const { return atomIds_; }

    // Recursively encode a formula, returning the DIMACS literal that
    // represents its truth value.  Negative literals represent negation.
    int encode(const Fml& f) {
        if (!f) { int v = allocId(); clauses_.push_back({v}); return v; }

        auto cit = cache_.find(f.get());
        if (cit != cache_.end()) return cit->second;

        int result = 0;
        switch (f->kind) {
        case FKind::Top:
            result = allocId();
            clauses_.push_back({result});       // unit clause: var must be true
            break;
        case FKind::Bot:
            result = allocId();
            clauses_.push_back({-result});      // unit clause: var must be false
            break;
        case FKind::Atom:
            result = getOrAllocAtom(f->name);
            break;
        case FKind::Not:
            result = -encode(f->child);         // negation = flipped literal
            break;
        case FKind::And: {
            // Tseitin for conjunction:
            //   x <-> (a1 & a2 & ... & an)
            //   Clauses:  (x -> ai) for each i,  and  (a1 & ... & an -> x)
            std::vector<int> sub;
            for (auto& c : f->children) sub.push_back(encode(c));
            if (sub.size() == 1) { result = sub[0]; break; }
            result = allocId();
            for (int lit : sub) clauses_.push_back({-result, lit});
            std::vector<int> big = {result};
            for (int lit : sub) big.push_back(-lit);
            clauses_.push_back(big);
            break;
        }
        case FKind::Or: {
            // Tseitin for disjunction:
            //   x <-> (a1 | a2 | ... | an)
            //   Clauses:  (ai -> x) for each i,  and  (x -> a1 | ... | an)
            std::vector<int> sub;
            for (auto& c : f->children) sub.push_back(encode(c));
            if (sub.size() == 1) { result = sub[0]; break; }
            result = allocId();
            for (int lit : sub) clauses_.push_back({result, -lit});
            std::vector<int> big = {-result};
            for (int lit : sub) big.push_back(lit);
            clauses_.push_back(big);
            break;
        }
        }
        cache_[f.get()] = result;
        return result;
    }
};

// ===========================================================================
// QBFProblem  (three-block  ∃ ∀ ∃  prefix)
//
// Used by the InputSymbolic encoding.  After Tseitin encoding, auxiliary
// variables are appended to the innermost existential block.
// ===========================================================================

struct QBFProblem {
    Fml matrix;
    std::vector<std::string> outerExist;  // first  ∃ block  (strategy vars)
    std::vector<std::string> universal;   // ∀ block         (input vars)
    std::vector<std::string> innerExist;  // second ∃ block  (annotations)
};

// Serialise a QBFProblem to QDIMACS text.
inline std::string toQDIMACS(const QBFProblem& prob) {
    TseitinEncoder enc;

    // Reserve atom IDs in quantifier-block order so that each block
    // occupies a contiguous range of IDs.
    for (auto& n : prob.outerExist)  enc.reserveAtom(n);
    for (auto& n : prob.universal)   enc.reserveAtom(n);
    for (auto& n : prob.innerExist)  enc.reserveAtom(n);
    int reserved = enc.numVars();

    int topLit = enc.encode(prob.matrix);

    // IDs allocated during encode() beyond `reserved` are Tseitin aux vars.
    std::vector<int> auxIds;
    for (int i = reserved + 1; i <= enc.numVars(); ++i) auxIds.push_back(i);

    std::ostringstream out;

    // symbol table (comment lines mapping names to IDs)
    for (auto& [name, id] : enc.atomMap())
        out << "c " << name << " " << id << "\n";

    int numClauses = (int)enc.clauses().size() + 1;  // +1 for top-level unit
    out << "p cnf " << enc.numVars() << " " << numClauses << "\n";

    // quantifier blocks
    auto writeBlock = [&](const char* pfx, const std::vector<std::string>& vars) {
        if (vars.empty()) return;
        out << pfx;
        for (auto& n : vars) out << " " << enc.atomId(n);
        out << " 0\n";
    };
    writeBlock("e", prob.outerExist);
    writeBlock("a", prob.universal);

    // inner existential = declared inner vars + Tseitin auxiliaries
    out << "e";
    for (auto& n : prob.innerExist) out << " " << enc.atomId(n);
    for (int id : auxIds) out << " " << id;
    out << " 0\n";

    // CNF clauses
    for (auto& cl : enc.clauses()) {
        for (int lit : cl) out << lit << " ";
        out << "0\n";
    }
    out << topLit << " 0\n";   // top-level assertion

    return out.str();
}

// ===========================================================================
// DQBFProblem  (dependency-quantified, Henkin prefix)
//
// Used by the StateSymbolic and Symbolic encodings.  Each existential
// variable carries an explicit list of universal variables it depends on.
// Tseitin auxiliary variables are declared with "e" (depend on everything).
// ===========================================================================

struct DQBFProblem {
    Fml matrix;
    std::vector<std::string> universalVars;
    struct DepVar {
        std::string name;
        std::vector<std::string> deps;  // names of universal vars
    };
    std::vector<DepVar> existentialVars;
    // Pairs of existential variables that represent the same function
    // on renamed universal arguments (for solver hints, e.g. pedant).
    std::vector<std::pair<std::string, std::string>> equivalentVars;
};

// Serialise a DQBFProblem to DQDIMACS text.
inline std::string toDQDIMACS(const DQBFProblem& prob) {
    TseitinEncoder enc;

    for (auto& n : prob.universalVars) enc.reserveAtom(n);
    for (auto& dv : prob.existentialVars) enc.reserveAtom(dv.name);
    int reserved = enc.numVars();

    int topLit = enc.encode(prob.matrix);

    std::vector<int> auxIds;
    for (int i = reserved + 1; i <= enc.numVars(); ++i) auxIds.push_back(i);

    std::ostringstream out;

    // symbol table
    for (auto& [name, id] : enc.atomMap())
        out << "c " << name << " " << id << "\n";

    int numClauses = (int)enc.clauses().size() + 1;
    out << "p cnf " << enc.numVars() << " " << numClauses << "\n";

    // universal variables
    out << "a";
    for (auto& n : prob.universalVars) out << " " << enc.atomId(n);
    out << " 0\n";

    // per-variable dependency declarations
    for (auto& dv : prob.existentialVars) {
        out << "d " << enc.atomId(dv.name);
        for (auto& dep : dv.deps) out << " " << enc.atomId(dep);
        out << " 0\n";
    }

    // Tseitin auxiliaries depend on all universals (free existential)
    if (!auxIds.empty()) {
        out << "e";
        for (int id : auxIds) out << " " << id;
        out << " 0\n";
    }

    // equivalence hints (for solvers like pedant)
    for (auto& [a, b] : prob.equivalentVars)
        out << "c= " << enc.atomId(a) << " " << enc.atomId(b) << " 0\n";

    // CNF clauses
    for (auto& cl : enc.clauses()) {
        for (int lit : cl) out << lit << " ";
        out << "0\n";
    }
    out << topLit << " 0\n";

    return out.str();
}

// ===========================================================================
// Encoding 1:  InputSymbolic   (QBF / QDIMACS)
//
// System states are *explicit* (enumerated 0..bound-1).
// Inputs are universally quantified propositional variables.
//
// Variables:
//   l_<s>_<q>           lambda: system state s is labelled with aut state q
//   ls_<s>_<q>_<bit>    ranking counter bits
//   t_<s>_<sp>          transition from s to sp is active
//   <output>_<s>        output value at system state s
//
// Quantifier prefix  (Mealy semantics):
//   ∃ λ, λ#            -- annotations (don't depend on current input)
//   ∀ inputs
//   ∃ τ, outputs        -- strategy (may depend on current input)
//
// For Moore, outputs move to the outer ∃ block (no input dependence).
//
// Ranking:  SCC-optimised.  The ranking constraint only applies to
// transitions within the same SCC that contains a rejecting state.
//
// Corresponds to Sources/BoundedSynthesis/InputSymbolicEncoding.swift.
// ===========================================================================

inline QBFProblem buildInputSymbolicQBF(const CoBuchiAutomaton& aut,
                                        const Specification& spec,
                                        int bound)
{
    QBFProblem prob;
    int nbits = numBitsNeeded(bound);

    // --- variable naming helpers ---
    auto lam  = [](int s, const std::string& q) {
        return "l_" + std::to_string(s) + "_" + q; };
    auto lsBit = [](int s, const std::string& q, int b) {
        return "ls_" + std::to_string(s) + "_" + q + "_" + std::to_string(b); };
    auto tau  = [](int s, int sp) {
        return "t_" + std::to_string(s) + "_" + std::to_string(sp); };
    auto outv = [](const std::string& name, int s) {
        return name + "_" + std::to_string(s); };

    // Replace output signal names with state-indexed versions.
    // In guards/safety conditions, "grant" at state 2 becomes "grant_2".
    auto substOut = [&](const Fml& f, int s) {
        return substitute(f, [&](const std::string& n) -> Fml {
            for (auto& o : spec.outputs)
                if (n == o) return fAtom(outv(n, s));
            return fAtom(n);
        });
    };

    std::vector<Fml> conj;

    // --- initial state labelling ---
    // System state 0 must be labelled with every initial automaton state.
    for (auto& q : aut.initialStates)
        conj.push_back(fAtom(lam(0, q)));

    // --- per-state constraints ---
    for (int s = 0; s < bound; ++s) {
        // At least one outgoing transition must be active.
        std::vector<Fml> ex;
        for (int sp = 0; sp < bound; ++sp) ex.push_back(fAtom(tau(s, sp)));
        conj.push_back(fOr(ex));

        for (auto& q : aut.states) {
            std::vector<Fml> inner;

            // Safety condition for automaton state q (if any).
            auto sc = aut.safetyConditions.find(q);
            if (sc != aut.safetyConditions.end())
                inner.push_back(substOut(sc->second, s));

            // Automaton transitions from q.
            auto tr = aut.transitions.find(q);
            if (tr != aut.transitions.end()) {
                for (auto& [qp, guard] : tr->second) {
                    // For each possible successor system state sp:
                    //   tau(s,sp) -> (lambda(sp,q') & ranking)
                    std::vector<Fml> perSP;
                    for (int sp = 0; sp < bound; ++sp) {
                        Fml lamNext = fAtom(lam(sp, qp));

                        // Ranking constraint (only within rejecting SCCs).
                        Fml rank = fTop();
                        bool need = !aut.isStateInNonRejectingSCC(q)
                                 && !aut.isStateInNonRejectingSCC(qp)
                                 && aut.isInSameSCC(q, qp);
                        if (need) {
                            std::vector<Fml> bitsNext, bitsCur;
                            for (int b = 0; b < nbits; ++b) {
                                bitsNext.push_back(fAtom(lsBit(sp, qp, b)));
                                bitsCur.push_back(fAtom(lsBit(s, q, b)));
                            }
                            bool strict = aut.rejectingStates.count(qp) > 0;
                            rank = strict ? bvGreater(bitsNext, bitsCur)
                                          : bvGreaterOrEqual(bitsNext, bitsCur);
                        }
                        perSP.push_back(fImplies(fAtom(tau(s, sp)),
                                                 fAnd(lamNext, rank)));
                    }
                    Fml tc = fAnd(perSP);
                    if (guard->kind == FKind::Top)
                        inner.push_back(tc);
                    else
                        inner.push_back(fImplies(substOut(guard, s), tc));
                }
            }
            // lambda(s,q) -> (safety & transition constraints)
            conj.push_back(fImplies(fAtom(lam(s, q)), fAnd(inner)));
        }
    }

    prob.matrix = fAnd(conj);

    // --- collect variable names for the quantifier blocks ---
    std::vector<std::string> lambdaVars, lsVars, tauVars, outVars;

    for (int s = 0; s < bound; ++s)
        for (auto& q : aut.states)
            lambdaVars.push_back(lam(s, q));

    for (int s = 0; s < bound; ++s)
        for (auto& q : aut.states)
            for (int b = 0; b < nbits; ++b)
                lsVars.push_back(lsBit(s, q, b));

    for (int s = 0; s < bound; ++s)
        for (int sp = 0; sp < bound; ++sp)
            tauVars.push_back(tau(s, sp));

    for (auto& o : spec.outputs)
        for (int s = 0; s < bound; ++s)
            outVars.push_back(outv(o, s));

    if (spec.semantics == Specification::Mealy) {
        prob.outerExist = lambdaVars;
        prob.outerExist.insert(prob.outerExist.end(), lsVars.begin(), lsVars.end());
        prob.universal = spec.inputs;
        prob.innerExist = tauVars;
        prob.innerExist.insert(prob.innerExist.end(), outVars.begin(), outVars.end());
    } else {
        prob.outerExist = lambdaVars;
        prob.outerExist.insert(prob.outerExist.end(), lsVars.begin(), lsVars.end());
        prob.outerExist.insert(prob.outerExist.end(), outVars.begin(), outVars.end());
        prob.universal = spec.inputs;
        prob.innerExist = tauVars;
    }

    return prob;
}

// ===========================================================================
// Encoding 2:  StateSymbolic   (DQBF / DQDIMACS)
//
// System states are encoded as bit-vectors (symbolic).
// Automaton states are still enumerated explicitly -- each gets its own
// lambda / lambdaSharp existential function.
//
// Universal variables:   s-bits, sp-bits, inputs
//
// Existential functions with dependency sets:
//   l_<q>_s    (depends on s-bits)     -- lambda at current state
//   l_<q>_sp   (depends on sp-bits)    -- lambda at next state
//   ls_<q>_<b>_s / _sp                 -- ranking counter bits
//   tau<j>     (depends on s + inputs) -- transition function
//   <output>   (depends on s [+inputs])-- output function
//
// The same function is applied to both current-state bits (s) and
// next-state bits (sp).  A *consistency constraint* ensures that
// if s == sp then the two applications agree:
//   (s0 <-> sp0) & ... & (sk <-> spk) -> (l_q_s <-> l_q_sp)
//
// Ranking is SCC-optimised, same as InputSymbolic.
//
// Corresponds to Sources/BoundedSynthesis/StateSymbolicEncoding.swift.
// ===========================================================================

inline DQBFProblem buildStateSymbolicDQBF(const CoBuchiAutomaton& aut,
                                          const Specification& spec,
                                          int bound)
{
    DQBFProblem prob;
    int nb = numBitsNeeded(bound);

    // variable name helpers
    auto sB  = [](int i) { return "s"  + std::to_string(i); };
    auto spB = [](int i) { return "sp" + std::to_string(i); };
    auto tB  = [](int i) { return "tau" + std::to_string(i); };
    auto lamS  = [](const std::string& q) { return "l_" + q + "_s"; };
    auto lamSP = [](const std::string& q) { return "l_" + q + "_sp"; };
    auto lsS   = [](const std::string& q, int b) {
        return "ls_" + q + "_" + std::to_string(b) + "_s"; };
    auto lsSP  = [](const std::string& q, int b) {
        return "ls_" + q + "_" + std::to_string(b) + "_sp"; };

    // --- universal variables ---
    std::vector<std::string> sVars, spVars;
    for (int i = 0; i < nb; ++i) { sVars.push_back(sB(i)); spVars.push_back(spB(i)); }
    prob.universalVars = sVars;
    prob.universalVars.insert(prob.universalVars.end(), spVars.begin(), spVars.end());
    prob.universalVars.insert(prob.universalVars.end(),
                              spec.inputs.begin(), spec.inputs.end());

    // --- existential functions with dependencies ---
    auto addDep = [&](const std::string& name, const std::vector<std::string>& deps) {
        prob.existentialVars.push_back({name, deps});
    };

    for (auto& q : aut.states) {
        addDep(lamS(q),  sVars);
        addDep(lamSP(q), spVars);
        prob.equivalentVars.push_back({lamS(q), lamSP(q)});
    }
    for (auto& q : aut.states)
        for (int b = 0; b < nb; ++b) {
            addDep(lsS(q, b),  sVars);
            addDep(lsSP(q, b), spVars);
            prob.equivalentVars.push_back({lsS(q, b), lsSP(q, b)});
        }

    std::vector<std::string> tauDeps = sVars;
    tauDeps.insert(tauDeps.end(), spec.inputs.begin(), spec.inputs.end());
    for (int i = 0; i < nb; ++i)
        addDep(tB(i), tauDeps);

    std::vector<std::string> outDeps = sVars;
    if (spec.semantics == Specification::Mealy)
        outDeps.insert(outDeps.end(), spec.inputs.begin(), spec.inputs.end());
    for (auto& o : spec.outputs)
        addDep(o, outDeps);

    // --- helper: formula asserting that bit-vector equals integer val ---
    auto encodeState = [&](const std::string& /*base*/, int val,
                           const std::function<std::string(int)>& bitName) {
        std::string bin = binaryFrom(val, nb);
        std::vector<Fml> bits;
        for (int j = 0; j < nb; ++j) {
            Fml v = fAtom(bitName(j));
            bits.push_back(bin[j] == '1' ? v : fNot(v));
        }
        return fAnd(bits);
    };

    std::vector<Fml> precond, matrix, consistency;

    // --- preconditions: exclude invalid bit-patterns ---
    for (int i = bound; i < (1 << nb); ++i) {
        precond.push_back(fNot(encodeState("s", i, sB)));
        precond.push_back(fNot(encodeState("sp", i, spB)));
        matrix.push_back(fNot(encodeState("tau", i, tB)));
    }

    // --- initial state: s=0 -> lambda(q_init, s) ---
    Fml sIsZero = encodeState("s", 0, sB);
    for (auto& q : aut.initialStates)
        matrix.push_back(fImplies(sIsZero, fAtom(lamS(q))));

    // --- tau-next-state assertion: sp_j <-> tau_j ---
    std::vector<Fml> tauEq;
    for (int j = 0; j < nb; ++j)
        tauEq.push_back(fIff(fAtom(spB(j)), fAtom(tB(j))));
    Fml spEqTau = fAnd(tauEq);

    // --- per-automaton-state constraints ---
    for (auto& q : aut.states) {
        std::vector<Fml> inner;

        auto sc = aut.safetyConditions.find(q);
        if (sc != aut.safetyConditions.end())
            inner.push_back(sc->second);   // outputs are DQBF function vars

        auto tr = aut.transitions.find(q);
        if (tr != aut.transitions.end()) {
            for (auto& [qp, guard] : tr->second) {
                Fml lamNext = fAtom(lamSP(qp));

                Fml rank = fTop();
                bool need = !aut.isStateInNonRejectingSCC(q)
                         && !aut.isStateInNonRejectingSCC(qp)
                         && aut.isInSameSCC(q, qp);
                if (need) {
                    std::vector<Fml> bN, bC;
                    for (int b = 0; b < nb; ++b) {
                        bN.push_back(fAtom(lsSP(qp, b)));
                        bC.push_back(fAtom(lsS(q, b)));
                    }
                    bool strict = aut.rejectingStates.count(qp) > 0;
                    rank = strict ? bvGreater(bN, bC)
                                  : bvGreaterOrEqual(bN, bC);
                }

                Fml tc = fImplies(spEqTau, fAnd(lamNext, rank));

                if (guard->kind == FKind::Top)
                    inner.push_back(tc);
                else
                    inner.push_back(fImplies(guard, tc));
            }
        }

        if (!inner.empty())
            matrix.push_back(fImplies(fAtom(lamS(q)), fAnd(inner)));
    }

    // --- function consistency constraints ---
    std::vector<Fml> sEqSp;
    for (int j = 0; j < nb; ++j)
        sEqSp.push_back(fIff(fAtom(sB(j)), fAtom(spB(j))));
    Fml statesMatch = fAnd(sEqSp);

    for (auto& q : aut.states) {
        consistency.push_back(
            fImplies(statesMatch, fIff(fAtom(lamS(q)), fAtom(lamSP(q)))));
        for (int b = 0; b < nb; ++b)
            consistency.push_back(
                fImplies(statesMatch, fIff(fAtom(lsS(q, b)), fAtom(lsSP(q, b)))));
    }

    // --- assemble: (precond -> matrix) & consistency ---
    std::vector<Fml> all;
    if (!precond.empty())
        all.push_back(fImplies(fAnd(precond), fAnd(matrix)));
    else
        all.push_back(fAnd(matrix));
    all.insert(all.end(), consistency.begin(), consistency.end());
    prob.matrix = fAnd(all);

    return prob;
}

// ===========================================================================
// Encoding 3:  Fully Symbolic   (DQBF / DQDIMACS)
//
// Both system states AND automaton states are encoded as bit-vectors.
// This yields a single lambda function  l(q-bits, s-bits)  and a
// single lambdaSharp function  ls(q-bits, s-bits),  instead of one
// per automaton state.
//
// The automaton transition relation is encoded as a global disjunction
// (delta), and the ranking uses a global rejecting predicate rather
// than SCC-based optimisation.
//
// Universal variables:  s-bits, sp-bits, q-bits, qp-bits, inputs
//
// Existential functions:
//   l_cur   (depends on q + s bits)
//   l_next  (depends on qp + sp bits)
//   ls_<b>_cur / _next              -- ranking counter bits
//   tau<j>  (depends on s + inputs)
//   <output> (depends on s [+inputs])
//
// Consistency: (q==qp & s==sp) -> (l_cur <-> l_next)  [and same for ls]
//
// Corresponds to Sources/BoundedSynthesis/SymbolicEncoding.swift.
// ===========================================================================

inline DQBFProblem buildSymbolicDQBF(const CoBuchiAutomaton& aut,
                                     const Specification& spec,
                                     int bound)
{
    DQBFProblem prob;

    // Fix automaton state ordering (std::set iterates in sorted order).
    std::vector<std::string> autStates(aut.states.begin(), aut.states.end());
    int numSys = numBitsNeeded(bound);
    int numAut = numBitsNeeded((int)autStates.size());
    int numRank = numBitsNeeded(bound);

    // --- variable name helpers ---
    auto sB  = [](int i) { return "s"  + std::to_string(i); };
    auto spB = [](int i) { return "sp" + std::to_string(i); };
    auto qB  = [](int i) { return "q"  + std::to_string(i); };
    auto qpB = [](int i) { return "qp" + std::to_string(i); };
    auto tB  = [](int i) { return "tau" + std::to_string(i); };

    // --- universal variable name vectors ---
    std::vector<std::string> sVars, spVars, qVars, qpVars;
    for (int i = 0; i < numSys; ++i) { sVars.push_back(sB(i));  spVars.push_back(spB(i)); }
    for (int i = 0; i < numAut; ++i) { qVars.push_back(qB(i));  qpVars.push_back(qpB(i)); }

    prob.universalVars = sVars;
    prob.universalVars.insert(prob.universalVars.end(), spVars.begin(), spVars.end());
    prob.universalVars.insert(prob.universalVars.end(), qVars.begin(), qVars.end());
    prob.universalVars.insert(prob.universalVars.end(), qpVars.begin(), qpVars.end());
    prob.universalVars.insert(prob.universalVars.end(),
                              spec.inputs.begin(), spec.inputs.end());

    // --- existential functions with dependencies ---
    auto addDep = [&](const std::string& name, const std::vector<std::string>& deps) {
        prob.existentialVars.push_back({name, deps});
    };

    // lambda depends on (q-bits, s-bits), applied to (q,s) and (qp,sp)
    std::vector<std::string> qsDeps, qpspDeps;
    qsDeps.insert(qsDeps.end(), qVars.begin(), qVars.end());
    qsDeps.insert(qsDeps.end(), sVars.begin(), sVars.end());
    qpspDeps.insert(qpspDeps.end(), qpVars.begin(), qpVars.end());
    qpspDeps.insert(qpspDeps.end(), spVars.begin(), spVars.end());

    addDep("l_cur",  qsDeps);
    addDep("l_next", qpspDeps);
    prob.equivalentVars.push_back({"l_cur", "l_next"});

    for (int b = 0; b < numRank; ++b) {
        std::string cur  = "ls_" + std::to_string(b) + "_cur";
        std::string next = "ls_" + std::to_string(b) + "_next";
        addDep(cur,  qsDeps);
        addDep(next, qpspDeps);
        prob.equivalentVars.push_back({cur, next});
    }

    std::vector<std::string> tauDeps = sVars;
    tauDeps.insert(tauDeps.end(), spec.inputs.begin(), spec.inputs.end());
    for (int i = 0; i < numSys; ++i)
        addDep(tB(i), tauDeps);

    std::vector<std::string> outDeps = sVars;
    if (spec.semantics == Specification::Mealy)
        outDeps.insert(outDeps.end(), spec.inputs.begin(), spec.inputs.end());
    for (auto& o : spec.outputs)
        addDep(o, outDeps);

    // --- helper: formula asserting that bit-vector equals integer val ---
    auto encodeBits = [](int val, int nbits,
                         const std::function<std::string(int)>& bitName) {
        std::string bin = binaryFrom(val, nbits);
        std::vector<Fml> bits;
        for (int j = 0; j < nbits; ++j) {
            Fml v = fAtom(bitName(j));
            bits.push_back(bin[j] == '1' ? v : fNot(v));
        }
        return fAnd(bits);
    };

    std::vector<Fml> precond, matrix, consistency;

    // --- preconditions: exclude invalid bit-patterns ---
    for (int i = bound; i < (1 << numSys); ++i) {
        precond.push_back(fNot(encodeBits(i, numSys, sB)));
        precond.push_back(fNot(encodeBits(i, numSys, spB)));
        matrix.push_back(fNot(encodeBits(i, numSys, tB)));
    }
    for (int i = (int)autStates.size(); i < (1 << numAut); ++i) {
        precond.push_back(fNot(encodeBits(i, numAut, qB)));
        precond.push_back(fNot(encodeBits(i, numAut, qpB)));
    }

    // --- initial state: (s=0 & q in initial) -> l_cur ---
    Fml sIsZero = encodeBits(0, numSys, sB);
    std::vector<Fml> initAut;
    for (auto& q : aut.initialStates) {
        int idx = (int)(std::find(autStates.begin(), autStates.end(), q) - autStates.begin());
        initAut.push_back(encodeBits(idx, numAut, qB));
    }
    matrix.push_back(fImplies(fAnd(sIsZero, fOr(initAut)), fAtom("l_cur")));

    // --- automaton transition relation (delta) ---
    // delta = OR over all edges (q=source & guard & qp=target)
    std::vector<Fml> deltas;
    std::vector<Fml> safetyParts;

    for (auto& q : autStates) {
        int qIdx = (int)(std::find(autStates.begin(), autStates.end(), q)
                         - autStates.begin());
        Fml qMatch = encodeBits(qIdx, numAut, qB);

        auto sc = aut.safetyConditions.find(q);
        if (sc != aut.safetyConditions.end())
            safetyParts.push_back(fImplies(qMatch, sc->second));

        auto tr = aut.transitions.find(q);
        if (tr == aut.transitions.end()) continue;
        for (auto& [qp, guard] : tr->second) {
            int qpIdx = (int)(std::find(autStates.begin(), autStates.end(), qp)
                              - autStates.begin());
            Fml qpMatch = encodeBits(qpIdx, numAut, qpB);

            if (guard->kind == FKind::Top)
                deltas.push_back(fAnd(qMatch, qpMatch));
            else
                deltas.push_back(fAnd({qMatch, guard, qpMatch}));
        }
    }
    Fml delta = fOr(deltas);

    // --- rejecting predicate: is qp a rejecting state? ---
    std::vector<Fml> rejParts;
    for (auto& rs : aut.rejectingStates) {
        int idx = (int)(std::find(autStates.begin(), autStates.end(), rs)
                        - autStates.begin());
        rejParts.push_back(encodeBits(idx, numAut, qpB));
    }
    Fml rejecting = rejParts.empty() ? fBot() : fOr(rejParts);

    // --- tau-next-state assertion: sp_j <-> tau_j ---
    std::vector<Fml> tauEq;
    for (int j = 0; j < numSys; ++j)
        tauEq.push_back(fIff(fAtom(spB(j)), fAtom(tB(j))));
    Fml spEqTau = fAnd(tauEq);

    // --- ranking (global, not SCC-optimised) ---
    std::vector<Fml> lsNext, lsCur;
    for (int b = 0; b < numRank; ++b) {
        lsNext.push_back(fAtom("ls_" + std::to_string(b) + "_next"));
        lsCur.push_back(fAtom("ls_" + std::to_string(b) + "_cur"));
    }
    Fml ranking = fAnd(
        fImplies(rejecting, bvGreater(lsNext, lsCur)),
        fImplies(fNot(rejecting), bvGreaterOrEqual(lsNext, lsCur))
    );

    // --- main transition constraint ---
    // (l_cur & delta & sp=tau) -> (l_next & ranking)
    matrix.push_back(
        fImplies(fAnd({fAtom("l_cur"), delta, spEqTau}),
                 fAnd(fAtom("l_next"), ranking))
    );

    // --- safety: l_cur -> AND(q=qi -> safety_i) ---
    if (!safetyParts.empty())
        matrix.push_back(fImplies(fAtom("l_cur"), fAnd(safetyParts)));

    // --- function consistency ---
    // (q==qp & s==sp) -> (l_cur <-> l_next)   [and same for each ls bit]
    std::vector<Fml> allMatch;
    for (int j = 0; j < numAut; ++j)
        allMatch.push_back(fIff(fAtom(qB(j)), fAtom(qpB(j))));
    for (int j = 0; j < numSys; ++j)
        allMatch.push_back(fIff(fAtom(sB(j)), fAtom(spB(j))));
    Fml argsMatch = fAnd(allMatch);

    consistency.push_back(
        fImplies(argsMatch, fIff(fAtom("l_cur"), fAtom("l_next"))));
    for (int b = 0; b < numRank; ++b)
        consistency.push_back(
            fImplies(argsMatch,
                     fIff(fAtom("ls_" + std::to_string(b) + "_cur"),
                          fAtom("ls_" + std::to_string(b) + "_next"))));

    // --- assemble: (precond -> matrix) & consistency ---
    std::vector<Fml> all;
    if (!precond.empty())
        all.push_back(fImplies(fAnd(precond), fAnd(matrix)));
    else
        all.push_back(fAnd(matrix));
    all.insert(all.end(), consistency.begin(), consistency.end());
    prob.matrix = fAnd(all);

    return prob;
}
