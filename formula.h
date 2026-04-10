// formula.h -- Propositional logic formula representation
//
// Formulas are immutable DAGs built from shared_ptr<const Formula>.
// The type alias `Fml` is used throughout the codebase.
//
// Constructors (fTop, fBot, fAtom, fNot, fAnd, fOr, fImplies, fIff)
// perform basic simplifications inline:
//   - fNot(Top) = Bot,  fNot(Not(x)) = x       (double negation)
//   - fAnd flattens nested Ands, short-circuits on Bot, drops Tops
//   - fOr  flattens nested Ors,  short-circuits on Top, drops Bots
//   - fImplies(a,b) desugars to  Or(Not(a), b)
//   - fIff(a,b)     desugars to  And(Implies(a,b), Implies(b,a))
//
// These formulas are later converted to CNF via the Tseitin encoder
// in encoding.h and serialised as QDIMACS or DQDIMACS.
//
// Corresponds to the Logic protocol + Proposition / Literal /
// BinaryOperator / UnaryOperator types in the original BoSy Swift
// source (Sources/Logic/Logic.swift).

#pragma once
#include <memory>
#include <string>
#include <vector>
#include <set>
#include <functional>

// Node types for the formula DAG.
enum class FKind { Top, Bot, Atom, Not, And, Or };

struct Formula {
    FKind kind;
    std::string name;                              // only used by Atom
    std::shared_ptr<const Formula> child;           // only used by Not
    std::vector<std::shared_ptr<const Formula>> children; // used by And, Or
};

// The handle type used everywhere.  Formulas are immutable once built.
using Fml = std::shared_ptr<const Formula>;

// --- Constant constructors (singletons) ---

inline Fml fTop() {
    static auto t = std::make_shared<Formula>(Formula{FKind::Top, {}, nullptr, {}});
    return t;
}

inline Fml fBot() {
    static auto b = std::make_shared<Formula>(Formula{FKind::Bot, {}, nullptr, {}});
    return b;
}

// --- Atom: a named propositional variable ---

inline Fml fAtom(const std::string& name) {
    return std::make_shared<Formula>(Formula{FKind::Atom, name, nullptr, {}});
}

// --- Negation (with double-negation elimination) ---

inline Fml fNot(Fml f) {
    if (!f) return nullptr;
    switch (f->kind) {
    case FKind::Top: return fBot();
    case FKind::Bot: return fTop();
    case FKind::Not: return f->child;   // !!x = x
    default:
        return std::make_shared<Formula>(Formula{FKind::Not, {}, f, {}});
    }
}

// --- N-ary conjunction (flattening + short-circuit) ---

inline Fml fAnd(std::vector<Fml> ops) {
    std::vector<Fml> flat;
    for (auto& o : ops) {
        if (!o || o->kind == FKind::Bot) return fBot();   // x & false = false
        if (o->kind == FKind::Top) continue;              // x & true  = x
        if (o->kind == FKind::And)
            flat.insert(flat.end(), o->children.begin(), o->children.end());
        else
            flat.push_back(o);
    }
    if (flat.empty()) return fTop();       // empty conjunction = true
    if (flat.size() == 1) return flat[0];
    return std::make_shared<Formula>(Formula{FKind::And, {}, nullptr, std::move(flat)});
}

inline Fml fAnd(Fml a, Fml b) { return fAnd(std::vector<Fml>{a, b}); }

// --- N-ary disjunction (flattening + short-circuit) ---

inline Fml fOr(std::vector<Fml> ops) {
    std::vector<Fml> flat;
    for (auto& o : ops) {
        if (!o || o->kind == FKind::Top) return fTop();
        if (o->kind == FKind::Bot) continue;
        if (o->kind == FKind::Or)
            flat.insert(flat.end(), o->children.begin(), o->children.end());
        else
            flat.push_back(o);
    }
    if (flat.empty()) return fBot();       // empty disjunction = false
    if (flat.size() == 1) return flat[0];
    return std::make_shared<Formula>(Formula{FKind::Or, {}, nullptr, std::move(flat)});
}

inline Fml fOr(Fml a, Fml b) { return fOr(std::vector<Fml>{a, b}); }

// --- Derived connectives ---

inline Fml fImplies(Fml a, Fml b) { return fOr(fNot(a), b); }
inline Fml fIff(Fml a, Fml b) { return fAnd(fImplies(a, b), fImplies(b, a)); }

// --- Utility: collect all atom names occurring in a formula ---

inline void collectAtoms(const Fml& f, std::set<std::string>& out) {
    if (!f) return;
    switch (f->kind) {
    case FKind::Atom: out.insert(f->name); break;
    case FKind::Not: collectAtoms(f->child, out); break;
    case FKind::And: case FKind::Or:
        for (auto& c : f->children) collectAtoms(c, out);
        break;
    default: break;
    }
}

// --- Utility: substitute atoms using a mapping function ---
//
// The mapper receives an atom name and returns its replacement Fml.
// Used by the InputSymbolic encoding to rename output propositions
// per system state (e.g. "grant" -> "grant_2").

inline Fml substitute(const Fml& f,
                      const std::function<Fml(const std::string&)>& mapper) {
    if (!f) return nullptr;
    switch (f->kind) {
    case FKind::Atom: return mapper(f->name);
    case FKind::Not: return fNot(substitute(f->child, mapper));
    case FKind::And: {
        std::vector<Fml> cs;
        for (auto& c : f->children) cs.push_back(substitute(c, mapper));
        return fAnd(cs);
    }
    case FKind::Or: {
        std::vector<Fml> cs;
        for (auto& c : f->children) cs.push_back(substitute(c, mapper));
        return fOr(cs);
    }
    default: return f;
    }
}
