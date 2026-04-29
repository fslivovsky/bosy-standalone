# Subformula-tableau encoding — current state

This document records the status of the `--encoding subformula` and the
experimental `--encoding subformula-bicond` paths in this repo, along
with the limitations we've identified and what would be required to lift
them.

## What's implemented

### `--encoding subformula` (working, sound, incomplete on assumption-guarantee specs)

A direct alternating-co-Büchi tableau encoding of NNF(φ). Skolem
functions live in the DQBF; one-way implications only.

- LTL parser, NNF, subformula closure: `ltl.h`.
- Encoding: `buildSubformulaTableauDQBF` in `encoding.h`.
- Two universal input sets (`σ_cur`, `σ_next`). Necessary so that an
  `X` over an input atom refers to the *next* step's input, not the
  current one.
- Existential pairs `λ_<id>_cur(s, σ_cur)`, `λ_<id>_next(sp, σ_next)`
  per *temporal* subformula (`U`, `R`, `F`, `G`); `c=` equivalence and
  the `(s == sp ∧ σ_cur == σ_next) → (cur ↔ next)` consistency clause
  tie them as the same Skolem applied at different argument tuples.
- `X` is inlined (not given a Skolem):
  `expand(X ψ', "cur") = spEqTau → expand(ψ', "next")`. Avoids the
  conflict of independent `X`-obligations in biconditionals like
  `X locked ↔ X hl_0`. Nested `X X` is rejected at encode time.
- Outputs are full Mealy when the spec is Mealy: `o_cur(s, σ_cur)` /
  `o_next(sp, σ_next)`, paired and consistent.
- Eventualities (`F`, `U`) carry per-(state, input) ranking counters
  with strict increase along the "delay" branch.

This encoding agrees with `--encoding symbolic` on simple safety and
single-G/single-F specs, on `amba_decomposed_shift`, and on basic
`X`-of-input / `X`-of-output examples.

### `--encoding subformula-bicond` (BROKEN — leave disabled or remove)

An attempt at a NuSMV-style satellite tableau with one Skolem per
subformula and **biconditional** rules. Implementation in
`buildSubformulaBicondDQBF` (`encoding.h`).

This regresses on cases the one-way encoding handles. On
`amba_decomposed_shift` it returns UNSAT at every bound where
`--encoding subformula` returns SAT at bound 2, because the
biconditional for any subformula whose RHS depends on σ_next (via the
inlined `X`) collapses to UNSAT — see the next section.

**Recommendation:** either delete `buildSubformulaBicondDQBF` and the
`--encoding subformula-bicond` flag, or document it as a non-working
experiment. Do not enable it for users.

## Empirical comparison (pedant, single-shot per bound)

| spec | b | one-way | bicond | symbolic |
|---|---|---|---|---|
| simple `G(req → F grant)` | 1 | SAT | SAT | SAT |
| amba\_decomposed\_shift | 1 | UNSAT | UNSAT | UNSAT |
| amba\_decomposed\_shift | 2 | **SAT** | **UNSAT** ✗ | SAT |
| amba\_decomposed\_shift | 4 | SAT | UNSAT ✗ | SAT |
| amba\_decomposed\_lock\_2 | 1 | UNSAT | UNSAT | UNSAT |
| amba\_decomposed\_lock\_2 | 2 | UNSAT | UNSAT | UNSAT |
| amba\_decomposed\_lock\_2 | 4 | **UNSAT** ✗ | UNSAT | **SAT** |

(✗ = wrong verdict.)

The one-way encoding is sound but incomplete — it returns UNSAT on
some specs that are realisable (`amba_decomposed_lock_2`). The
bicond encoding is strictly worse.

## Why simple biconditionals don't work in single-step bounded synthesis

In NuSMV-style **bounded model checking**, each `x_ψ(t)` is a *fresh
variable per time step*, so a biconditional like

    x_aUb(t) ↔ x_b(t) ∨ (x_a(t) ∧ x_aUb(t+1))

ties three independent variables. Tractable.

In **bounded synthesis** with a one-step DQBF encoding, `x_ψ_cur(s, σ_cur)`
and `x_ψ_next(sp, σ_next)` are pair-wise equivalent applications of the
*same* Skolem function `x_ψ(state, input)`. The matrix is universally
quantified over `(s, sp, σ_cur, σ_next)`. The biconditional

    x_G(s, σ_cur) ↔ body(s, σ_cur, σ_next) ∧ (spEqTau → x_G(sp, σ_next))

has to hold for **every** σ_next. The LHS is a single value of
`x_G(s, σ_cur)`. The RHS depends on σ_next — both directly (via the
inlined `X` inside `body`) and via `x_G(sp, σ_next)`. For different
σ_next at the same (s, σ_cur), the RHS takes different values, so the
biconditional collapses to UNSAT.

The one-way `→` is consistent because it only says "if `x_G` is true
at (s, σ_cur), then the RHS holds for every σ_next" — an obligation
the synthesiser can satisfy. Going to `↔` adds the converse "if
the RHS holds for some σ_next then `x_G` is true," which is
incompatible with `x_G` being σ_next-independent.

## Why the one-way encoding is incomplete on assumption-guarantee specs

For φ = `(G a) → (G b)`, NNF gives `F(¬a) ∨ G(b)`, a top-level
disjunction. The encoding's initial constraint at s=0 evaluates this
inline:

    (s = 0) → (λ_F(0, σ_cur) ∨ λ_G(0, σ_cur))

The synthesiser, per σ_cur, picks one disjunct. If it picks `λ_G`,
the G-rule propagates uniformly: λ_G(s, σ_cur) → ∀ σ_next: λ_G(sp,
σ_next). Under cur/next equivalence, λ_G is forced *true* at (sp, σ_next)
for every σ_next — including σ_next that violate the assumption. At
those, the body of `G b` is unsatisfiable (e.g., requires
`locked = hl_0` and `locked = hl_1` simultaneously).

The synthesiser would *want* to switch back to the F-branch on
assumption-violating σ_next, but the OR-choice was only available at
s=0; once λ_G is propagated, it is uniformly true at sp regardless of
the next input. State-and-input dependent λ captures the *current*
input but not the suffix of the trace.

The automaton-based path (`--encoding symbolic`) sidesteps this
because Spot's Büchi automaton for ¬φ folds the assumption into every
transition guard: on a σ_next that violates the assumption, no
transition fires, and λ is simply not propagated to that letter. The
implication is absorbed into the automaton structure rather than left
as a top-level Boolean OR.

## What would actually fix the assumption-guarantee case

Three real designs, in increasing order of effort:

1. **Use `--encoding symbolic`.** Spot's `ltl2tgba` already does the
   right thing structurally. This is the recommended escape hatch
   today.

2. **Antichain-based annotation.** Replace each per-subformula λ with
   a Boolean indicator over *subsets* of subformulas (one bit per
   subformula, jointly representing the run-tree's currently active
   set). This is the symbolic Miyano–Hayashi state, and it admits
   Schewe–Finkbeiner-style bounded annotation cleanly. Worst-case
   exponential in |Sub(φ)|, often much smaller.

3. **Multi-step (k-step + lasso) BMC-style unrolling.** Introduce
   per-step variables `x_ψ(t)` for t = 0..k; transitions stitch
   consecutive steps; lasso closure handles infinite traces. Each
   `x_ψ(t)` is a *fresh* variable, so biconditionals are sound. This
   is the NuSMV-satellite approach done correctly. Substantially more
   complex encoding, but principled.

## Recommended next step

If the goal is to make `--encoding subformula` correct on
assumption-guarantee benchmarks, option (2) above is the most
promising — it preserves the compactness motivation of the subformula
tableau (linear in |Sub(φ)| per system state, with subset bits) while
fixing the trace-dependent OR-branch choice that currently breaks. It
is also what most "alternating to non-alternating" arguments in the
literature reduce to.

Until that's done, treat `--encoding subformula` as a fast,
auxiliary path useful on safety/liveness specs without top-level
assumption-guarantee implications, and route the remaining benchmarks
through `--encoding symbolic`.
