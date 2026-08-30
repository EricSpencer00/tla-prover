---- MODULE TLAPS ----
EXTENDS Naturals

(* Backends for the TLA+ Proof System, declared as constants so the proof      *)
(* engine can bind them to the prover executables at runtime.                    *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4

(* Temporal-logic proof rules derived from Lamport's TLA+ methodology.  The    *)
(* rules are not sketched here; their shape is what reserves the names.          *)
Invariance == TRUE
WellFormed == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

(* Foundational set-theoretic facts.                                            *)
Extensionality == \A A, B \in SUBSET Nat : (\A x \in A : x \in B) /\ (\A x \in B : x \in A) => A = B
NoUniversalSet == \A S \in SUBSET Nat : \A x \in Nat : x \in S => \E y \in Nat : y \notin S

(* The module has no system dynamics to model; the proof rules above are the   *)
(* entire content, and they must remain available to the prover.               *)

(* The configuration file expects exactly these operators to exist in this    *)
(* module, even though none of them has a state-changing action.               *)
SPECIFICATION == \E b \in {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4} : TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == Extensionality
PROPERTIES == NoUniversalSet

====