---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(*  TLAPS: Backend Pragmas for the TLA Proof System (TLAPS)                *)
(*  This module declares operators that act as configuration directives   *)
(*  for the various automated theorem provers and SMT solvers used by     *)
(*  TLAPS.  It also states two fundamental theorems that are always true *)
(*  in standard set theory.                                                *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\*  Backend prover configuration operators
\*  (All are no‑ops at the level of the model; they are meant for the     *)
\*   proof manager to interpret.)                                         
\* ----------------------------------------------------------------------
Zenon(t)    == TRUE
Isabelle(t) == TRUE
CVC3(t)     == TRUE
Yices(t)    == TRUE
VeriT(t)    == TRUE
Z3(t)       == TRUE
SPASS(t)    == TRUE
LS4(t)      == TRUE

\* ----------------------------------------------------------------------
\*  Temporal logic proof rule names (reserved, no semantics here)
\* ----------------------------------------------------------------------
InvRule      == TRUE   \* Invariance rule
WFRule       == TRUE   \* Weak fairness rule
SFRule       == TRUE   \* Strong fairness rule
Simulation   == TRUE   \* Step simulation rule
WellFormed   == TRUE   \* Well‑formedness rule

\* ----------------------------------------------------------------------
\*  Fundamental theorems
\* ----------------------------------------------------------------------
EXTENSIONALITY == 
  \A X, Y \in SUBSET UNIV : (\A z \in UNIV : (z \in X) <=> (z \in Y)) => X = Y

NO_SET_CONTAINS_ALL == 
  \A S \in SUBSET UNIV : \E v \in UNIV : v \notin S

\* ----------------------------------------------------------------------
\*  Specification (trivial – there are no state variables or actions)
\* ----------------------------------------------------------------------
VARIABLES dummy

Init == dummy = 0

Next == dummy' = dummy

\* The specification encompasses Init and the stuttering Next.
Spec == Init /\ [][Next]_<<dummy>>

\* ----------------------------------------------------------------------
\*  Exported identifiers required by the (empty) .cfg
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INIT          == Init
NEXT          == Next
INVARIANTS    == EXTENSIONALITY
PROPERTIES    == NO_SET_CONTAINS_ALL

=============================================================================