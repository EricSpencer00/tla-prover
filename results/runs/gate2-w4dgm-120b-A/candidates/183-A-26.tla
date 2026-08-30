---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets, TLC

(* Backends for the TLA Proof System: identifiers that instruct TLAPS to    *)
(* dispatch proof obligations to various provers/solvers.                    *)
Zenon == "zenon"
Isabelle == "isabelle"
CVC3 == "cvc3"
Yices == "yices"
veriT == "verit"
Z3 == "z3"
SPASS == "spass"
LS4 == "ls4"

(* Foundational temporal logic proof rules from Lamport's TLA+ paper.  The    *)
(* module body is empty; these names are reserved to prevent future clashes. *)
Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

(* Set extensionality: two sets with identical elements are equal.            *)
Extensionality == \A A, B \in SUBSET {1, 2, 3} : (A = B) <=> (\A x \in {1, 2, 3} : (x \in A) <=> (x \in B))

(* No set contains every possible value.                                      *)
NotUniversal == {1, 2, 3} \notin SUBSET {1, 2, 3}

CONSTANTS

Specification == Extensionality /\ NotUniversal

Init == Specification /\ TRUE

Next == Spec == Specification

Invariants == Extensionality

Properties == NotUniversal
====