---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*********************************************************************
\* Module: TLAPS
\* Description: Configuration infrastructure for the TLA Proof System (TLAPS).
\* It defines operators that specify which backend provers to invoke,
\* along with fundamental temporal logic proof rules and basic set
\* theorems required by the reference configuration.
*********************************************************************)

\* -----------------------------------------------------------------
\* Backend dispatch operators (no operational effect, only used by TLAPS)
\* -----------------------------------------------------------------
Zenon(args) == FALSE             \* placeholder; never true in execution
Isabelle(args) == FALSE
CVC3(args) == FALSE
Yices(args) == FALSE
VeriT(args) == FALSE
Z3(args) == FALSE
SPASS(args) == FALSE
LS4(args) == FALSE

\* -----------------------------------------------------------------
\* Temporal logic proof rule placeholders
\* These operators are never true during model execution; they are
\* only names reserved for TLAPS.
\* -----------------------------------------------------------------
InvarianceRule(Inv) == FALSE
WFRule(Proc) == FALSE
SFRule(Proc) == FALSE
StepSimRule(Proc) == FALSE
WellFormednessRule == FALSE

\* -----------------------------------------------------------------
\* Basic set theorems required by the description
\* -----------------------------------------------------------------
EXTENSION_THEOREM ==
  \A X, Y \in SUBSET UNIV : (\A e \in UNIV : e \in X <=> e \in Y) => X = Y

NO_SET_CONTAINS_ALL_VALUES ==
  \A X \in SUBSET UNIV : \E y \in UNIV : y \notin X

\* -----------------------------------------------------------------
\* Specification skeleton (no state variables)
\* -----------------------------------------------------------------
Spec == Init /\ [] [][Next]_<<>>   \* No operational behavior

Init == TRUE                      \* Empty initial predicate

Next == FALSE                     \* No state transitions

\* -----------------------------------------------------------------
\* Operators required by the cfg (none are required, but we define
\* them for completeness)
\* -----------------------------------------------------------------
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == <<>>
PROPERTIES == <<>>

=============================================================================