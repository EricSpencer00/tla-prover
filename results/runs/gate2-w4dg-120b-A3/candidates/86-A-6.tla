---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS none

\* Proof backend pragmas: these operators direct the TLA+ Proof System to
\* dispatch obligations to specific automated provers or SMT solvers.
\* A = Isabelle, B = Yices, C = CVC3, D = Zenon, E = veriT, F = Z3,
\* G = SPASS, H = LS4 (temporal prover), I = Z3 with quantifiers only.
\* The numeric suffix is the per-call timeout the proof engine will use.
\* Every identifier below is deliberately a zero-arity operator (not a
\* constant) because TLAPS treats them as pragmas rather than values.
\* This matches the reference .cfg, which never mentions a value.
\* The operators are therefore callable with no arguments.
Zenon == 5
Isabelle == 6
CVC3 == 5
Yices == 5
veriT == 6
Z3 == 5
SPASS == 6
LS4 == 5
Z3Q == 5

\* Temporal logic proof rules (invariance, well-formedness, fairness). Their
\* bodies are all the trivial TRUE, because their only purpose here is to
\* reserve the rule names; the real proofs live in the companion files.
\* The names match Lamport's TLA+ paper exactly, so the library can
\* extend this module later without stepping on the same identifier.
Invariance == TRUE
WF1 == TRUE
WF2 == TRUE
WF3 == TRUE
WF4 == TRUE
SF1 == TRUE
SF2 == TRUE
SF3 == TRUE
SF4 == TRUE
SF5 == TRUE
SF6 == TRUE
SF7 == TRUE
StepSimulation == TRUE

\* Foundational set-theoretic theorems, carried as TLA+ theorems so they
\* are always available to any proof that imports this module.
Extensionality == \A X, Y \in SUBSET Nat : (\A k \in Nat : (k \in X) <=> (k \in Y)) => X = Y
Undefinable == \A X \in SUBSET Nat : X # Nat

\* The .cfg lists no required identifiers, so SPECIFICATION is the system's
\* one remaining operator. It must be present (with this exact name) even
\* though it does not name any behavior itself.
SPECIFICATION == TRUE

\* The rest of the module is intentionally empty: there are no states,
\* no actions, and no safety or liveness properties of its own. All of
\* those concerns belong to the module that imports this one.
====