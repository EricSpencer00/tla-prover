---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Backend pragma operators for TLAPS.  They are defined as identity
  operators; the actual dispatch to provers is performed by TLAPS.
--------------------------------------------------------------------*)

Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
veriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

(*--------------------------------------------------------------------
  Reserved temporal‑logic proof‑rule names.  They are defined as
  uninterpreted operators (identity) so that their names are
  reserved for future use.
--------------------------------------------------------------------*)

Invariance(p) == p
WellFormed(p) == p
StrongFairness(p) == p
WeakFairness(p) == p
StepSimulation(p) == p

(*--------------------------------------------------------------------
  Fundamental theorems required by the description.
--------------------------------------------------------------------*)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAll ==
  \A S \in SUBSET UNIV : ~ (UNIV \subseteq S)

====