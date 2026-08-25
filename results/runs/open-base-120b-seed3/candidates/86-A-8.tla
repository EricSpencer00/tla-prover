---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Backend pragma operators – placeholders that allow the proof
  system to recognize the names of the various automated provers.
-----------------------------------------------------------------*)
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)    == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule names – defined as identity operators
  so that their identifiers are reserved for future use.
-----------------------------------------------------------------*)
InvarianceRule(p)        == p
WellFormednessRule(p)   == p
StrongFairnessRule(p)   == p
WeakFairnessRule(p)     == p
StepSimulationRule(p)   == p

(*-----------------------------------------------------------------
  Fundamental theorems required by the description.
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) = (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

(*-----------------------------------------------------------------
  Minimal specification skeleton – the module has no state
  variables, so INIT and NEXT are simply TRUE, and SPECIFICATION
  is the usual temporal composition of these.
-----------------------------------------------------------------*)
INIT == TRUE
NEXT == TRUE
SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == {}
PROPERTIES == {}
====