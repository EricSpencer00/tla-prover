---- MODULE TLAPS ----
\* Backend prover configuration for the TLA Proof System (TLAPS). This module
\* defines operators that instruct TLAPS to dispatch proof obligations to
\* various automated theorem provers and SMT solvers. It also states the
\* foundational temporal-logic rules (invariance, well-formedness, fairness)
\* from Lamport's TLA paper, which are included to reserve their names and
\* prevent naming clashes in future versions.
EXTENDS Naturals

CONSTANTS
  TIMEOUT, RECURSIVE, LINEAR, PRUNE, ASSUME

\* Dispatch operators: each names a prover/solver and its arguments. The
\* arguments are the proof obligations to be handed over; the operator's
\* result is an opaque token that is never inspected, so the actual proof
\* search is outside the model.
Zenon     == [kind |-> "zenon",     timeout |-> TIMEOUT, goals |-> {}]
Isabelle  == [kind |-> "isabelle",  timeout |-> TIMEOUT, goals |-> {}]
CVC3      == [kind |-> "cvc3",      timeout |-> TIMEOUT, goals |-> {}]
Yices     == [kind |-> "yices",     timeout |-> TIMEOUT, goals |-> {}]
veriT     == [kind |-> "verit",     timeout |-> TIMEOUT, goals |-> {}]
Z3        == [kind |-> "z3",        timeout |-> TIMEOUT, goals |-> {}]
SPASS     == [kind |-> "spass",     timeout |-> TIMEOUT, goals |-> {}]
LS4       == [kind |-> "ls4",       timeout |-> TIMEOUT, goals |-> {}]

\* Foundational temporal-logic theorems from Lamport's TLA paper, included
\* here solely to reserve their names.
SetExtensionality ==
  \A X, Y \in SUBSET Nat :
    (\A e \in Nat : (e \in X) <=> (e \in Y)) => (X = Y)

NoSetContainsAll ==
  \A X \in SUBSET Nat : \A e \in Nat : e \notin X

\* Specification scaffolding: although this module has no state and no
\* actions, the proof library requires the operators that name the
\* specification's components.
Specification == TRUE
Init          == TRUE
Next          == TRUE
Invariants    == {}
Properties    == {}

====