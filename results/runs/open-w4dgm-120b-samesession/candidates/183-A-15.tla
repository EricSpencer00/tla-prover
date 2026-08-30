---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers for the TLA+ proof system. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

(* Temporal logic proof rules used by the verifier. *)
CONSTANTS Invariance, Wf1, Wf2, StrongFairness, WeakFairness, StepSimulation

NoTimeout == 0

TypeOK ==
  /\ Zenon \in Nat /\ Isabelle \in Nat /\ CVC3 \in Nat
  /\ Yices \in Nat /\ veriT \in Nat /\ Z3 \in Nat /\ SPASS \in Nat /\ LS4 \in Nat

TimeoutsBounded == LS4 <= 3

TimeoutsWellFormed == LS4 = 0 \/ LS4 # 0

\* Core set-theoretic fact: two sets with the same elements are equal.
Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B

\* No set collects every natural number (boundedness of each).
NoUniversalSet == \A A \in SUBSET Nat : (\A x \in Nat : x \in A) => FALSE

Spec ==
  /\ TypeOK
  /\ TimeoutsBounded
  /\ TimeoutsWellFormed
  /\ Extensionality
  /\ NoUniversalSet
====