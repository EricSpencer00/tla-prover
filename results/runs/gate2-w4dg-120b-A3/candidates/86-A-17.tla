---- MODULE TLAPS ----
EXTENDS Naturals

\* This module defines backend pragmas for the TLA Proof System (TLAPS).  It
\* provides operators that direct TLAPS to dispatch proof obligations to
\* various theorem provers and SMT solvers (Zenon, Isabelle, CVC3, Yices,
\* veriT, Z3, SPASS, LS4) and also states basic proof rules for temporal
\* logic reasoning (invariance, well-formedness, fairness).  The SPECIFICATION
\* operator is defined to be the conjunction of the INIT and NEXT operators,
\* plus the set of basic invariants and additional theorems.
CONSTANTS NONE

InitRule == FALSE
InvariantRule == FALSE
Wf1Rule == FALSE
Wf2Rule == FALSE
Fairness1 == FALSE
Fairness2 == FALSE
Version == "1.0"

\* Reserved operators: SetExtensionality, NoSetContainsAll, and all the
\* backend operators below.  The invariance and fairness rules are included
\* so their names are reserved and cannot clash with names added later.
SetExtensionality == FALSE
NoSetContainsAll == FALSE
Zenon == FALSE
Isabelle == FALSE
CVC3 == FALSE
Yices == FALSE
VeriT == FALSE
Z3 == FALSE
SPASS == FALSE
LS4 == FALSE

Init == InitRule
Next == InvariantRule
TypeOK == TRUE
Spec == Init /\ [][Next]_NONE

Invariants == {SetExtensionality, NoSetContainsAll}
Properties == {Wf1Rule, Wf2Rule, Fairness1, Fairness2}

====