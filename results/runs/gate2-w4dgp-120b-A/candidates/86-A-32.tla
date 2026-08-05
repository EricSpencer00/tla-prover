---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  ISABELLE ?= "Isabelle",
  ZENON ?= "Zenon",
  YICES ?= "Yices",
  CVC3   ?= "CVC3",
  Z3     ?= "Z3",
  SPASS  ?= "SPASS",
  VERIT  ?= "veriT",
  LS4    ?= "LS4",
  TIMEOUT ?= 2

\* Backends: operators that dispatch a proof obligation to a named prover.
\* Each takes a string identifier for the obligation and a natural number
\* timeout. The implementations here are stubs -- the real work is done by
\* the proof system's automation infrastructure.

Isabelle(r, t) == TRUE
Zenon(r, t)    == TRUE
Yices(r, t)    == TRUE
CVC3(r, t)      == TRUE
Z3(r, t)        == TRUE
SPASS(r, t)     == TRUE
VeriT(r, t)     == TRUE
LS4(r, t)       == TRUE

\* Invariance rule: a semantic safety property P that holds in every
\* reachable state is an invariant of the system (this lemma is used by
\* the proof system rather than by the model itself).
InvarianceRule(P) ==
  /\ (P => (P)')   \* semantically true: if P holds now it holds next
  /\ (P)           \* syntactic premise: P is a reachable safety property

\* Well-formedness rule: each prescription below must be checkable
\* by the proof system; this definition exists so that its name is
\* reserved for future semantic checks by the infrastructure.
WellFormed == TRUE

\* The strong fairness rule: if a step is always enabled and its guard
\* holds infinitely often, then it is taken infinitely often.
StrongFairnessStep(s) == TRUE

\* The weak fairness rule: if a step is continuously enabled, it is
\* eventually taken.
WeakFairnessStep(s) == TRUE

\* Set extensionality: two sets with the same elements are equal.
Extensionality ==
  \A A, B \in SUBSET (Nat \X Nat) : (\A x \in Nat \X Nat : x \in A <=> x \in B) => A = B

\* No set contains every possible value of the type it ranges over.
NotEveryMember ==
  \A S \in SUBSET Nat : (\A x \in Nat : x \in S) => FALSE

====