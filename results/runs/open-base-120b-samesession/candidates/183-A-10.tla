---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Definition of the universal set (the set of all values).  
-----------------------------------------------------------------*)
UNIV == { x : TRUE }

(*-----------------------------------------------------------------
  Backend pragma operators for TLAPS.  They are defined as stubs
  that simply return TRUE; the proof manager interprets the
  applications of these operators.
-----------------------------------------------------------------*)
Zenon(expr, timeout)   == TRUE
Isabelle(expr, timeout)== TRUE
CVC3(expr, timeout)    == TRUE
Yices(expr, timeout)   == TRUE
VeriT(expr, timeout)   == TRUE
Z3(expr, timeout)      == TRUE
SPASS(expr, timeout)   == TRUE
LS4(expr, timeout)     == TRUE

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule operators (place‑holders).  
-----------------------------------------------------------------*)
InvRule(P)            == TRUE   \* invariance rule
WFRule(P)             == TRUE   \* weak fairness rule
SFRule(P)             == TRUE   \* strong fairness rule
StepRule(P, Q)        == TRUE   \* step‑simulation rule

(*-----------------------------------------------------------------
  Foundational theorems.
-----------------------------------------------------------------*)

THEOREM SetExtensionality ==
  \A A, B \in SUBSET UNIV :
    (\A x : (x \in A) <=> (x \in B)) => A = B

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV :
    ~(\A x : x \in S)

====