---- MODULE TLAPS ----
EXTENDS TLC

(***************************************************************
 * TLAPS Backend Pragmas and Temporal Logic Proof Rules Module *
 ***************************************************************)

\* -----------------------------------------------------------------
\* Operators for dispatching proof obligations to automated provers
\* -----------------------------------------------------------------
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

\* -----------------------------------------------------------------
\* Temporal logic proof rules (names reserved, no implementation)
\* -----------------------------------------------------------------
InvRule(Inv, Act) == Inv
WFRule(Act) == Act
WF1Rule(Inv, Act) == Inv
WF2Rule(Inv, Act) == Inv
SFRule(SF, Act) == SF
SF1Rule(Inv, Act) == Inv
SF2Rule(Inv, Act) == Inv

\* -----------------------------------------------------------------
\* Constants (none are required for this module)
\* -----------------------------------------------------------------
\* No constants are declared because the specification does not
\* introduce any state variables or parameters.

\* -----------------------------------------------------------------
\* Specification components required by the .cfg (none needed)
\* -----------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

\* -----------------------------------------------------------------
\* Safety theorems required by the description
\* -----------------------------------------------------------------
SetExtensionality == \A X, Y : (\A e : e \in X <=> e \in Y) => X = Y
NoUniversalSet == \A S : \E x : x \notin S

====