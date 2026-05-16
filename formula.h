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
#include <unordered_map>
#include <mutex>
#include <algorithm>

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

// --- Hash-consing caches ------------------------------------------------
//
// Constructors return a *shared* node for any logically-equal input, so
// equal subtrees have identical pointer identity.  This matters for the
// Tseitin encoder in encoding.h, whose memoisation cache is keyed by
// raw pointer: without interning, structurally-equal subterms (e.g. the
// same `lsBit(s,q,b)` atom built in different recursive `bvGreater`
// calls) are encoded into CNF independently and each gets a fresh aux
// variable.
//
// Caches are global and mutex-protected; construction is rare enough
// that contention is not a concern.  The caches keep nodes alive for
// the lifetime of the process, which is fine for the short-lived
// encoding runs of this tool.

namespace formula_detail {

inline std::mutex& cacheMutex() { static std::mutex m; return m; }

inline std::unordered_map<std::string, Fml>& atomCache() {
    static std::unordered_map<std::string, Fml> m; return m;
}

inline std::unordered_map<const Formula*, Fml>& notCache() {
    static std::unordered_map<const Formula*, Fml> m; return m;
}

// Key = canonical (sorted-by-pointer, deduplicated) child vector.
struct VecHash {
    size_t operator()(const std::vector<Fml>& v) const noexcept {
        size_t h = v.size();
        for (auto& f : v)
            h = h * 1315423911u ^ std::hash<const void*>()(f.get());
        return h;
    }
};
struct VecEq {
    bool operator()(const std::vector<Fml>& a, const std::vector<Fml>& b) const noexcept {
        if (a.size() != b.size()) return false;
        for (size_t i = 0; i < a.size(); ++i)
            if (a[i].get() != b[i].get()) return false;
        return true;
    }
};
using NaryCache = std::unordered_map<std::vector<Fml>, Fml, VecHash, VecEq>;
inline NaryCache& andCache() { static NaryCache m; return m; }
inline NaryCache& orCache()  { static NaryCache m; return m; }

} // namespace formula_detail

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
    std::lock_guard<std::mutex> lk(formula_detail::cacheMutex());
    auto& cache = formula_detail::atomCache();
    auto it = cache.find(name);
    if (it != cache.end()) return it->second;
    auto a = std::make_shared<Formula>(Formula{FKind::Atom, name, nullptr, {}});
    cache.emplace(name, a);
    return a;
}

// --- Negation (with double-negation elimination + hash-consing) ---

inline Fml fNot(Fml f) {
    if (!f) return nullptr;
    switch (f->kind) {
    case FKind::Top: return fBot();
    case FKind::Bot: return fTop();
    case FKind::Not: return f->child;   // !!x = x
    default: break;
    }
    std::lock_guard<std::mutex> lk(formula_detail::cacheMutex());
    auto& cache = formula_detail::notCache();
    auto it = cache.find(f.get());
    if (it != cache.end()) return it->second;
    auto n = std::make_shared<Formula>(Formula{FKind::Not, {}, f, {}});
    cache.emplace(f.get(), n);
    return n;
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
    // Canonicalise children (sort by pointer + dedup) so logically-equal
    // conjunctions share a single hash-consed node.
    std::sort(flat.begin(), flat.end(),
              [](const Fml& a, const Fml& b) { return a.get() < b.get(); });
    flat.erase(std::unique(flat.begin(), flat.end()), flat.end());
    if (flat.size() == 1) return flat[0];
    std::lock_guard<std::mutex> lk(formula_detail::cacheMutex());
    auto& cache = formula_detail::andCache();
    auto it = cache.find(flat);
    if (it != cache.end()) return it->second;
    auto n = std::make_shared<Formula>(Formula{FKind::And, {}, nullptr, flat});
    cache.emplace(std::move(flat), n);
    return n;
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
    std::sort(flat.begin(), flat.end(),
              [](const Fml& a, const Fml& b) { return a.get() < b.get(); });
    flat.erase(std::unique(flat.begin(), flat.end()), flat.end());
    if (flat.size() == 1) return flat[0];
    std::lock_guard<std::mutex> lk(formula_detail::cacheMutex());
    auto& cache = formula_detail::orCache();
    auto it = cache.find(flat);
    if (it != cache.end()) return it->second;
    auto n = std::make_shared<Formula>(Formula{FKind::Or, {}, nullptr, flat});
    cache.emplace(std::move(flat), n);
    return n;
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
