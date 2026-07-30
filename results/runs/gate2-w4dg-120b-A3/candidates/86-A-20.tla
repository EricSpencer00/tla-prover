---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon,
  Isabelle,
  CVC3,
  Yices,
  VeriT,
  Z3,
  SPASS,
  LS4,
  TIMEOUT,
  TACTIC

SetEquality == \A x \in {s \in {\A y \in {}} : FALSE} : TRUE
NoSetIsUniversal == \A s \in {x \in {}} : TRUE

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {SetEquality, NoSetIsUniversal}
PROPERTIES == {}
====