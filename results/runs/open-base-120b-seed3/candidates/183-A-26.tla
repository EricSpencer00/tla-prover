---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* -------------------------------------------------
\* Backend pragma placeholders for the TLAPS system
\* -------------------------------------------------
Zenon(op)    == op
Isabelle(op) == op
CVC3(op)     == op
Yices(op)    == op
VeriT(op)    == op
Z3(op)       == op
SPASS(op)    == op
LS4(op)      == op

\* -------------------------------------------------
\* Fundamental theorems
\* -------------------------------------------------
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) \<=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV : S # UNIV

\* -------------------------------------------------
\* Specification skeleton (no state variables)
\* -------------------------------------------------
SPECIFICATION == Init /\ [] (Next)

Init == TRUE

Next == TRUE

INVARIANTS == {}

PROPERTIES == {}

====