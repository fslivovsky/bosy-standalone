// automaton.h -- Co-Buechi automaton and LTL-to-automaton conversion
//
// This file provides:
//   1. A recursive-descent parser for propositional guard formulas in
//      the SPIN never-claim syntax (e.g. "(a) && !(b)").
//   2. The CoBuchiAutomaton struct with:
//        - Tarjan SCC computation  (used by the InputSymbolic and
//          StateSymbolic encodings for ranking optimisation)
//        - Rejecting-sink removal  (a preprocessing step that turns
//          trivial rejecting sinks into safety conditions)
//   3. A SPIN never-claim parser  (parseSpinNeverClaim)
//   4. An ltlToAutomaton() wrapper that shells out to Spot's ltl2tgba
//      with --spin output, then parses the result.
//
// Corresponds to:
//   Sources/Automata/CoBüchi.swift      (CoBüchiAutomaton)
//   Sources/Automata/Automaton.swift     (removeRejectingSinks)
//   Sources/Automata/Conversion.swift    (parseSpinNeverClaim, ltl2tgba call)
//   Sources/Logic/Logic.swift            (BooleanParser -- guard parsing)
//   Sources/Utils/Graph.swift            (Tarjan SCC -- trajan())

#pragma once
#include "formula.h"
#include <map>
#include <set>
#include <vector>
#include <string>
#include <sstream>
#include <stack>
#include <algorithm>
#include <stdexcept>
#include <cstdio>
#include <cstdlib>
#include <unistd.h>
#include <sys/wait.h>

// ===========================================================================
// Guard-formula parser  (propositional, SPIN never-claim syntax)
//
// Grammar:
//   expr     ::= and_expr ('||' and_expr)*
//   and_expr ::= unary    ('&&' unary)*
//   unary    ::= ('!' | '~') unary  |  primary
//   primary  ::= '(' expr ')'  |  '1' | '0' | 'true' | 'false'  |  ident
//
// Identifiers may contain  [a-zA-Z0-9_\[\]]  (covers signal names like
// "r_0" or "g[1]").  Single '&' / '|' are also accepted.
// ===========================================================================

namespace guard_parser {

inline void skipWs(const std::string& s, size_t& i) {
    while (i < s.size() && (s[i]==' '||s[i]=='\t'||s[i]=='\n'||s[i]=='\r')) ++i;
}

inline bool isIdChar(char c) {
    return (c>='a'&&c<='z')||(c>='A'&&c<='Z')||(c>='0'&&c<='9')
           ||c=='_'||c=='['||c==']';
}

inline bool matchStr(const std::string& s, size_t& i, const char* pat) {
    size_t len = std::string(pat).size();
    if (s.compare(i, len, pat) == 0) { i += len; skipWs(s, i); return true; }
    return false;
}

inline Fml parseExpr(const std::string& s, size_t& i);  // forward decl

inline Fml parsePrimary(const std::string& s, size_t& i) {
    skipWs(s, i);
    if (i >= s.size()) return fTop();

    if (s[i] == '(') {
        ++i; skipWs(s, i);
        Fml e = parseExpr(s, i);
        skipWs(s, i);
        if (i < s.size() && s[i] == ')') ++i;
        skipWs(s, i);
        return e;
    }
    if (s[i] == '1' && (i+1>=s.size() || !isIdChar(s[i+1]))) { ++i; skipWs(s,i); return fTop(); }
    if (s[i] == '0' && (i+1>=s.size() || !isIdChar(s[i+1]))) { ++i; skipWs(s,i); return fBot(); }
    if (matchStr(s, i, "true"))  return fTop();
    if (matchStr(s, i, "false")) return fBot();

    // identifier
    size_t start = i;
    while (i < s.size() && isIdChar(s[i])) ++i;
    if (i == start) throw std::runtime_error("guard parse error near: " + s.substr(i));
    std::string name = s.substr(start, i - start);
    skipWs(s, i);
    return fAtom(name);
}

inline Fml parseUnary(const std::string& s, size_t& i) {
    skipWs(s, i);
    if (i < s.size() && (s[i] == '!' || s[i] == '~')) {
        ++i; skipWs(s, i);
        return fNot(parseUnary(s, i));
    }
    return parsePrimary(s, i);
}

inline Fml parseAnd(const std::string& s, size_t& i) {
    Fml left = parseUnary(s, i);
    skipWs(s, i);
    while (i+1 < s.size() && s[i]=='&' && s[i+1]=='&') {
        i += 2; skipWs(s, i);
        left = fAnd(left, parseUnary(s, i));
        skipWs(s, i);
    }
    while (i < s.size() && s[i]=='&' && (i+1>=s.size() || s[i+1]!='&')) {
        ++i; skipWs(s, i);
        left = fAnd(left, parseUnary(s, i));
        skipWs(s, i);
    }
    return left;
}

inline Fml parseExpr(const std::string& s, size_t& i) {
    Fml left = parseAnd(s, i);
    skipWs(s, i);
    while (i+1 < s.size() && s[i]=='|' && s[i+1]=='|') {
        i += 2; skipWs(s, i);
        left = fOr(left, parseAnd(s, i));
        skipWs(s, i);
    }
    while (i < s.size() && s[i]=='|' && (i+1>=s.size() || s[i+1]!='|')) {
        ++i; skipWs(s, i);
        left = fOr(left, parseAnd(s, i));
        skipWs(s, i);
    }
    return left;
}

} // namespace guard_parser

inline Fml parseGuard(const std::string& s) {
    size_t i = 0;
    return guard_parser::parseExpr(s, i);
}

// ===========================================================================
// Co-Buechi Automaton
//
// A co-Buechi automaton accepts runs where the *rejecting* states are
// visited only finitely often.  In bounded synthesis the encoding adds
// a ranking function (lambdaSharp) that must strictly increase at
// rejecting transitions within the same SCC, ensuring finiteness.
//
// Fields:
//   states           -- all state names
//   initialStates    -- entry states
//   rejectingStates  -- states from "accept_*" labels in the never claim
//   transitions      -- transitions[src][tgt] = propositional guard
//   safetyConditions  -- per-state invariants (from removeRejectingSinks)
//   sccId / inRejectingScc -- populated by computeSCC()
// ===========================================================================

struct CoBuchiAutomaton {
    std::set<std::string> states;
    std::set<std::string> initialStates;
    std::set<std::string> rejectingStates;
    std::map<std::string, std::map<std::string, Fml>> transitions;
    std::map<std::string, Fml> safetyConditions;

    // SCC data (populated by computeSCC)
    std::map<std::string, int> sccId;
    std::map<std::string, bool> inRejectingScc;

    // True if state s belongs to an SCC that contains NO rejecting state.
    bool isStateInNonRejectingSCC(const std::string& s) const {
        auto it = inRejectingScc.find(s);
        return it != inRejectingScc.end() && !it->second;
    }

    // True if a and b are in the same SCC (or if SCC data is missing).
    bool isInSameSCC(const std::string& a, const std::string& b) const {
        auto ia = sccId.find(a), ib = sccId.find(b);
        if (ia == sccId.end() || ib == sccId.end()) return true;
        return ia->second == ib->second;
    }

    // ------- Tarjan SCC computation -------
    // Populates sccId and inRejectingScc for every state.
    void computeSCC() {
        int index = 0;
        std::stack<std::string> stk;
        std::map<std::string, int> idx, low;
        std::set<std::string> onStack;
        std::vector<std::vector<std::string>> sccs;

        std::function<void(const std::string&)> strongconnect =
            [&](const std::string& v) {
            idx[v] = low[v] = index++;
            stk.push(v); onStack.insert(v);

            auto it = transitions.find(v);
            if (it != transitions.end()) {
                for (auto& [w, _] : it->second) {
                    if (idx.find(w) == idx.end()) {
                        strongconnect(w);
                        low[v] = std::min(low[v], low[w]);
                    } else if (onStack.count(w)) {
                        low[v] = std::min(low[v], idx[w]);
                    }
                }
            }

            if (low[v] == idx[v]) {
                std::vector<std::string> comp;
                std::string w;
                do {
                    w = stk.top(); stk.pop();
                    onStack.erase(w);
                    comp.push_back(w);
                } while (w != v);
                sccs.push_back(comp);
            }
        };

        for (auto& s : states)
            if (idx.find(s) == idx.end())
                strongconnect(s);

        for (int i = 0; i < (int)sccs.size(); ++i) {
            bool hasRej = false;
            for (auto& s : sccs[i])
                if (rejectingStates.count(s)) hasRej = true;
            for (auto& s : sccs[i]) {
                sccId[s] = i;
                inRejectingScc[s] = hasRej;
            }
        }
    }

    // ------- Remove rejecting sinks -------
    // A rejecting sink is a rejecting state whose only outgoing
    // transition is a self-loop with guard True.  Such states can
    // never be left, so any run reaching them would violate co-Buechi
    // acceptance.  We remove the sink and convert each incoming
    // transition (guard g) into a safety condition (not g) on the
    // source state.
    void removeRejectingSinks() {
        std::vector<std::string> toRemove;
        for (auto& st : rejectingStates) {
            auto it = transitions.find(st);
            if (it == transitions.end()) continue;
            auto& out = it->second;
            if (out.size() != 1) continue;
            auto selfIt = out.find(st);
            if (selfIt == out.end()) continue;
            if (selfIt->second->kind != FKind::Top) continue;
            toRemove.push_back(st);
        }
        for (auto& st : toRemove) {
            if (st == "init") {
                safetyConditions[st] = fBot();
                continue;
            }
            rejectingStates.erase(st);
            states.erase(st);
            transitions.erase(st);
            for (auto& [src, out] : transitions) {
                auto tgt = out.find(st);
                if (tgt == out.end()) continue;
                Fml guardExpr = tgt->second;
                out.erase(tgt);
                Fml cond = safetyConditions.count(src) ? safetyConditions[src] : fTop();
                safetyConditions[src] = fAnd(cond, fNot(guardExpr));
            }
        }
    }
};

// ===========================================================================
// SPIN never-claim parser
//
// Parses the textual output of  `ltl2tgba -f '<ltl>' --spin`.
// State names are normalised by stripping "accept_" and "_init" affixes.
// States whose original name starts with "accept_" become rejecting;
// states whose original name ends with "_init" become initial.
//
// After parsing, removeRejectingSinks() and computeSCC() are called
// automatically.
// ===========================================================================

inline CoBuchiAutomaton parseSpinNeverClaim(const std::string& neverClaim) {
    CoBuchiAutomaton aut;
    std::string lastState;

    auto normalize = [](const std::string& name) -> std::string {
        std::string s = name;
        auto pos = s.find("accept_");
        if (pos == 0) s = s.substr(7);
        pos = s.find("_init");
        if (pos != std::string::npos && pos == s.size() - 5) s = s.substr(0, pos);
        return s;
    };

    std::istringstream iss(neverClaim);
    std::string line;
    while (std::getline(iss, line)) {
        // trim whitespace
        size_t a = line.find_first_not_of(" \t\r\n");
        if (a == std::string::npos) continue;
        line = line.substr(a);
        size_t b = line.find_last_not_of(" \t\r\n");
        if (b != std::string::npos) line = line.substr(0, b + 1);

        // skip structural lines
        if (line.empty() || line[0]=='{' || line[0]=='}' ||
            line.substr(0,5)=="never" || line.substr(0,2)=="if" ||
            line.substr(0,2)=="fi") continue;

        if (line.back() == ':') {
            // --- state declaration ---
            std::string orig = line.substr(0, line.size()-1);
            while (!orig.empty() && orig.back()==';') orig.pop_back();
            std::string name = normalize(orig);
            aut.states.insert(name);
            aut.transitions[name]; // ensure map entry exists
            lastState = name;
            if (orig.find("accept_") == 0 || orig.find("accept_") != std::string::npos)
                if (orig.substr(0, 7) == "accept_")
                    aut.rejectingStates.insert(name);
            if (orig.find("_init") != std::string::npos &&
                orig.size() >= 5 && orig.substr(orig.size()-5) == "_init")
                aut.initialStates.insert(name);
            if (orig == "accept_init") {
                aut.rejectingStates.insert(name);
                aut.initialStates.insert(name);
            }
        } else if (line.substr(0, 2) == "::") {
            // --- transition  ":: guard -> goto target" ---
            line = line.substr(2);
            size_t p = line.find_first_not_of(" \t");
            if (p != std::string::npos) line = line.substr(p);
            auto arrow = line.find(" -> goto ");
            if (arrow == std::string::npos) continue;
            std::string guardStr = line.substr(0, arrow);
            std::string target = line.substr(arrow + 9);
            while (!target.empty() && (target.back()==';'||target.back()==' '))
                target.pop_back();
            target = normalize(target);
            Fml guard = parseGuard(guardStr);
            aut.transitions[lastState][target] = guard;
        } else if (line.find("skip") != std::string::npos) {
            // "skip" is a self-loop with guard True
            aut.transitions[lastState][lastState] = fTop();
        }
    }

    if (aut.initialStates.empty())
        throw std::runtime_error("no initial state found in never claim");

    aut.removeRejectingSinks();
    aut.computeSCC();
    return aut;
}

// ===========================================================================
// LTL -> Automaton  (calls external ltl2tgba from the Spot library)
//
// Runs:  ltl2tgba -f '<negated LTL>' --spin --any --small
// and parses the resulting SPIN never-claim into a CoBuchiAutomaton.
// ===========================================================================

inline std::string shellEscape(const std::string& s) {
    std::string r = "'";
    for (char c : s) {
        if (c == '\'') r += "'\\''";
        else r += c;
    }
    r += "'";
    return r;
}

inline CoBuchiAutomaton ltlToAutomaton(const std::string& ltl,
                                       const std::string& ltl2tgba = "ltl2tgba") {
    std::string cmd = ltl2tgba + " -f " + shellEscape(ltl)
                      + " --spin --any --small 2>&1";
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) throw std::runtime_error("failed to run " + ltl2tgba);
    std::string output;
    char buf[4096];
    while (fgets(buf, sizeof(buf), pipe)) output += buf;
    int st = pclose(pipe);
    if (WEXITSTATUS(st) != 0)
        throw std::runtime_error(ltl2tgba + " failed:\n" + output);
    return parseSpinNeverClaim(output);
}
