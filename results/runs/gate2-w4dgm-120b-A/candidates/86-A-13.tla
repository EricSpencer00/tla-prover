---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(* TLAPS backend configuration: operators that dispatch proof obligations to
   various automated provers and solvers.  Also defined here are the basic
   temporal-logic proof rules (invariance, well-formedness, fairness) that
   come from Lamport's TLA+ paper; these are kept as named operators so
   their names are reserved and no future prover/backed module can clash
   with them.  The module is a library piece, not a system model: it
   declares no state and has no actions. *)

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Dispatch a TLA+ proof obligation to the listed backend prover/solver.
Dispatch(backend) == backend

\* Temporal logic proof rules -- reserved names only, no system modeled.
Invariance ==
  (\A s \in Nat : \A t \in Nat : s >= t => P(s) => P(t))

WellFormed ==
  (\A s \in Nat, e \in Nat :
     (\A k \in 0 .. e : P(s + k)) => (\A k \in 0 .. e : Q(s + k)))

StrongFairness ==
  (\A e \in Nat : (\A k \in 0 .. e : R(k)) \A f \in Nat : f >= e => R(f))

WeakFairness ==
  (\A e \in Nat : (\E k \in 0 .. e : S(k)) \A f \in Nat : f >= e => S(f))

StepSimulation ==
  (\A s \in Nat : \E t \in Nat : T(s, t)

\* Two theorems that the base library always states.
Extensionality ==
  \A A, B \in SUBSET Nat : (\A x \in Nat : (x \in A) <=> (x \in B)) => A = B

NotUniversal ==
  \A A \in SUBSET Nat : (\A x \in Nat : x \in A) => FALSE

\* No state, no actions: this module is a collection of named operators.
Spec == TRUE
Init == TRUE
Next == TRUE
Invariants == {}
Properties == {Extensionality, NotUniversal}

====