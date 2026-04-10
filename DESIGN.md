# bosy_standalone -- Design Document

A standalone C++17 reimplementation of the DQBF-based bounded-synthesis
pipeline from [BoSy](https://github.com/reactive-systems/bosy), with no
external library dependencies.  It reads a BoSy JSON specification,
converts the LTL formula to a co-Buechi automaton (via Spot's `ltl2tgba`),
encodes the bounded-synthesis problem as QBF or DQBF, and calls an
external solver.

## Building

```
make          # produces ./bosy_standalone
```

Requires a C++17 compiler (GCC 8+, Clang 7+).  No libraries needed.

## Usage

```bash
# QBF encoding with DepQBF
./bosy_standalone --solver ~/tools/depqbf/depqbf \
    --ltl2tgba ~/tools/bosy/Tools/ltl2tgba spec.json

# DQBF state-symbolic encoding with PEDANT
./bosy_standalone --encoding state-symbolic \
    --solver ~/tools/pedant/build/src/pedant spec.json

# DQBF fully-symbolic encoding
./bosy_standalone --encoding symbolic \
    --solver ~/tools/pedant/build/src/pedant spec.json

# Dump the encoding (no solver needed)
./bosy_standalone --dump --bound 3 spec.json > out.qdimacs

# TLSF input: convert with syfco first
syfco --format bosy spec.tlsf > spec.json
./bosy_standalone --solver ./solver spec.json
```

## File overview

```
standalone/
  Makefile       -- single-command build
  formula.h      -- propositional formula DAG  (Fml type)
  automaton.h    -- co-Buechi automaton, SPIN parser, ltl2tgba wrapper
  encoding.h     -- three encodings + Tseitin + QDIMACS/DQDIMACS output
  main.cpp       -- CLI, JSON parser, solver invocation, bound search
  DESIGN.md      -- this file
```

## Correspondence to BoSy Swift sources

| Standalone          | BoSy Swift source                                |
|---------------------|--------------------------------------------------|
| `formula.h`         | `Sources/Logic/Logic.swift` (Logic protocol, Proposition, Literal, BinaryOperator, UnaryOperator, `&`, `\|`, `-->`, `<->`, `!` operators) |
| `automaton.h` guard parser | `Sources/Logic/Logic.swift` (BooleanLexer, BooleanParser, ScalarScanner) |
| `automaton.h` CoBuchiAutomaton | `Sources/Automata/CoBüchi.swift` |
| `automaton.h` SCC    | `Sources/Utils/Graph.swift` (`trajan()`) |
| `automaton.h` removeRejectingSinks | `Sources/Automata/Automaton.swift` |
| `automaton.h` SPIN parser | `Sources/Automata/Conversion.swift` (`parseSpinNeverClaim`) |
| `automaton.h` ltlToAutomaton | `Sources/Automata/Conversion.swift` (`convertWithSpot`) |
| `encoding.h` numBitsNeeded, binaryFrom | `Sources/Utils/Function.swift` |
| `encoding.h` bvGreater/bvGreaterOrEqual | `Sources/Logic/Logic.swift` (`order()`) |
| `encoding.h` TseitinEncoder | `Sources/Logic/Transformer.swift` (DIMACSVisitor, QDIMACSVisitor) |
| `encoding.h` toQDIMACS | `Sources/Logic/Transformer.swift` (QDIMACSVisitor.description) |
| `encoding.h` toDQDIMACS | `Sources/Logic/Transformer.swift` (DQDIMACSVisitor.description) |
| `encoding.h` buildInputSymbolicQBF | `Sources/BoundedSynthesis/InputSymbolicEncoding.swift` |
| `encoding.h` buildStateSymbolicDQBF | `Sources/BoundedSynthesis/StateSymbolicEncoding.swift` |
| `encoding.h` buildSymbolicDQBF | `Sources/BoundedSynthesis/SymbolicEncoding.swift` |
| `main.cpp` parseSpec | `Sources/Specification/Specifications.swift` |
| `main.cpp` buildNegatedLTL | `Sources/BoSy/main.swift` (search function) |
| `main.cpp` runSolver | `Sources/Logic/Solver.swift` (QbfSolver, DqbfSolver) |

## Pipeline

```
spec.json
    |
    v
[parseSpec]  -->  Specification {semantics, inputs, outputs, assumptions, guarantees}
    |
    v
[buildNegatedLTL]  -->  "!(G(req -> F grant))"
    |
    v
[ltlToAutomaton]  ---(ltl2tgba --spin)--->  SPIN never claim  -->  [parseSpinNeverClaim]
    |
    v
CoBuchiAutomaton {states, initialStates, rejectingStates, transitions, safetyConditions}
    |  removeRejectingSinks()
    |  computeSCC()
    v
[encoding]  ---(one of three backends)--->  Fml (formula tree)
    |
    v
[Tseitin encoder]  -->  CNF clauses + quantifier/dependency info
    |
    v
[toQDIMACS / toDQDIMACS]  -->  text file
    |
    v
[external solver]  -->  SAT (realizable) / UNSAT (try next bound)
```

## The three encodings

### 1. InputSymbolic (QBF / QDIMACS)

- **System states**: explicit (0..bound-1)
- **Automaton states**: explicit (enumerated)
- **Quantifier prefix**: `exists lambda,lambdaSharp . forall inputs . exists tau,outputs`
- **Ranking**: SCC-optimised (only within rejecting SCCs)
- **Output format**: QDIMACS (three quantifier blocks)
- **Solver type**: QBF (e.g. DepQBF, CAQE, RAReQS)

Variables:
- `l_<s>_<q>` -- lambda: system state s labelled with automaton state q
- `ls_<s>_<q>_<bit>` -- ranking counter bits (co-Buechi acceptance)
- `t_<s>_<sp>` -- transition from s to sp
- `<output>_<s>` -- output value at state s

For Mealy semantics, tau and output variables are in the inner existential
block (after forall inputs), so they can depend on the current input.
For Moore, outputs move to the outer block.

### 2. StateSymbolic (DQBF / DQDIMACS)

- **System states**: symbolic bit-vector (`s0..s_{k-1}`)
- **Automaton states**: explicit (one lambda function per automaton state)
- **Quantifier prefix**: dependency-quantified (Henkin)
- **Ranking**: SCC-optimised
- **Output format**: DQDIMACS
- **Solver type**: DQBF (e.g. PEDANT, iDQ, HQS)

Each existential variable has an explicit dependency set:
- `l_<q>_s` depends on s-bits (current state)
- `l_<q>_sp` depends on sp-bits (next state)
- `tau<j>` depends on s-bits + inputs

These represent the *same function* applied to different arguments.
A consistency constraint ensures `(s == sp) -> (l_q_s <-> l_q_sp)`.

### 3. Symbolic (DQBF / DQDIMACS)

- **System states**: symbolic bit-vector
- **Automaton states**: symbolic bit-vector (`q0..q_{m-1}`)
- **Lambda**: single function `l(q-bits, s-bits)` for all automaton states
- **Ranking**: global rejecting predicate (no SCC optimisation)
- **Output format**: DQDIMACS
- **Solver type**: DQBF

The automaton transition relation is encoded as a disjunction `delta`
over all edges.  Rejecting states are characterised by a predicate on
the qp-bits, and the ranking constraint applies uniformly:
- `rejecting(qp) -> ls' > ls`  (strict increase)
- `!rejecting(qp) -> ls' >= ls` (non-decrease)

## Key design decisions

### Ranking direction

BoSy uses an *increasing* ranking function (counter goes up at rejecting
transitions).  Since the counter is bounded by `numBitsNeeded(bound)`
bits, it can only increase finitely many times, guaranteeing that
rejecting states are visited finitely often (co-Buechi acceptance).

The `bvGreater(a, b)` function encodes `a > b` as a propositional
formula via MSB-first lexicographic comparison.  This matches the
`order()` function in `Sources/Logic/Logic.swift`.

### Tseitin encoding

The `TseitinEncoder` converts an arbitrary formula DAG into an
equisatisfiable CNF by introducing one auxiliary variable per internal
node.  Pointer-based memoisation ensures each shared sub-DAG node is
encoded exactly once.

Variable IDs are assigned in two phases:
1. `reserveAtom()` pre-assigns IDs to known atoms (quantifier-block vars).
2. `encode()` allocates new IDs for Tseitin auxiliaries.

IDs beyond the reserved range are collected as Tseitin auxiliaries and
placed in the innermost existential block (QDIMACS) or the free
existential line (DQDIMACS).

### DQBF function consistency

In QBF, the alternating quantifier structure implicitly defines Skolem
functions.  In DQBF, each existential variable has an explicit
dependency set, but the solver doesn't inherently know that two
variables represent the *same function* applied to different arguments.

We enforce this with consistency constraints:
```
(args_current == args_next) -> (f_current <-> f_next)
```

For the StateSymbolic encoding, "args" are the system-state bits (s vs sp).
For the Symbolic encoding, "args" are both system and automaton state bits.

## What is NOT implemented

- **Solution extraction**: the tool reports REALIZABLE/UNREALIZABLE but
  does not extract an explicit transition system or AIGER circuit.
  BoSy uses certifying QBF solvers (CADET, QuAbS) for this.

- **Solution optimisation**: BoSy does a binary search on the number
  of AIGER gates to minimise the circuit.

- **HyperLTL support**: BoSy's `BoSyHyper` handles hyperproperties.

- **Game-based solving**: BoSy's `GameSolver` / `SafetyGameReduction`
  uses BDD-based safety-game solving (via CUDD) as an alternative to
  QBF/DQBF.

- **SMT encoding**: BoSy has an `SmtEncoding` that uses Z3/CVC4.

- **TLSF parsing**: use `syfco --format bosy` to convert TLSF to JSON.

## Extending this code

### Adding a new encoding

1. Define a function `buildFooEncoding(aut, spec, bound)` returning
   either `QBFProblem` or `DQBFProblem`.
2. Add a new `ENC_FOO` case in `main.cpp`'s `EncKind` enum and wire
   it into the dump/search switch statements.

### Adding solution extraction

The `TseitinEncoder::atomMap()` provides the mapping from variable
names to DIMACS IDs.  After a SAT result, parse the solver's
certificate (e.g. AIGER from CADET/QuAbS) and use the atom map to
recover the values of tau and output variables.
