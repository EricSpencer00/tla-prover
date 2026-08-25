---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT U

(*--------------------------------------------------------------------
  Backend provers: operators that act as TLAPS pragmas.
--------------------------------------------------------------------*)
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

(*--------------------------------------------------------------------
  Temporal‑logic proof rules (names only; bodies are placeholders).
--------------------------------------------------------------------*)
Invariant(P) == P
WellFormed(P) == P
StrongFairness(P) == P
WeakFairness(P) == P
StepSimulation(P) == P

(*--------------------------------------------------------------------
  Fundamental theorems.
--------------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T \in SUBSET U :
    (\A x \in U : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET U : \E x \in U : x \notin S

====