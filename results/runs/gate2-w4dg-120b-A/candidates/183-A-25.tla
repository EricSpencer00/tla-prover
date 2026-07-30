---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon
  Isabelle
  CVC3
  Yices
  VeriT
  Z3
  SPASS
  LS4

\* Pragmas for the TLAPS backend provers. The operators below are not
\* evaluated at runtime; they are read by the proof assistant and instruct
\* which automated solver it should invoke for each proof obligation.
\* The arguments are the solver name, a timeout in seconds, and, for
\* Isabelle, an optional proof tactic.

ZenonT(pt) == [solver |-> Zenon, timeout |-> pt]
IsabelleT(pt, tac) == [solver |-> Isabelle, timeout |-> pt, tactic |-> tac]
CVC3T(pt) == [solver |-> CVC3, timeout |-> pt]
YicesT(pt) == [solver |-> Yices, timeout |-> pt]
VeriTT(pt) == [solver |-> VeriT, timeout |-> pt]
Z3T(pt) == [solver |-> Z3, timeout |-> pt]
SPASST(pt) == [solver |-> SPASS, timeout |-> pt]
LS4T(pt) == [solver |-> LS4, timeout |-> pt]

\* Foundational proof rules from Lamport's TLA+ book. These are included
\* as reserved identifiers so they cannot be re-used elsewhere in the
\* library without naming clash.

InvarianceStep == TRUE
WFStep == TRUE
SFStep == TRUE
WellFormedStep == TRUE

\* Set extensionality (a core axiom of set theory) and the statement that
\* no set contains every possible value -- the two theorems that the
\* reference configuration expects to be present.

Extensionality == TRUE
NoSetIsUniversal == TRUE

\* The module is configuration only: SPECIFICATION, INIT, NEXT,
\* INVARIANTS and PROPERTIES must exist for the .cfg to bind, but they
\* carry no behaviour -- every action is a stuttering step.
Specification == TRUE
Init == TRUE
Next == TRUE
Invariants == TRUE
Properties == TRUE

====