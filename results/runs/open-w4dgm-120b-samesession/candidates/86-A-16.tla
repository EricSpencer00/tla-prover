---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  o1, o2, o3, o4, o5, o6, o7, o8,
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

PROBLEMS == {o1, o2, o3, o4, o5, o6, o7, o8}

VARIABLES assigned

vars == <<assigned>>

TypeOK ==
  /\ assigned \subseteq PROBLEMS
  /\ assigned \cap (PROBLEMS \ assigned) = {}

Init ==
  /\ assigned = {}

AssignZenon ==
  /\ o1 \notin assigned
  /\ assigned' = assigned \cup {o1}

AssignIsabelle ==
  /\ o2 \notin assigned
  /\ assigned' = assigned \cup {o2}

AssignCVC3 ==
  /\ o3 \notin assigned
  /\ assigned' = assigned \cup {o3}

AssignYices ==
  /\ o4 \notin assigned
  /\ assigned' = assigned \cup {o4}

AssignVeriT ==
  /\ o5 \notin assigned
  /\ assigned' = assigned \cup {o5}

AssignZ3 ==
  /\ o6 \notin assigned
  /\ assigned' = assigned \cup {o6}

AssignSPASS ==
  /\ o7 \notin assigned
  /\ assigned' = assigned \cup {o7}

AssignLS4 ==
  /\ o8 \notin assigned
  /\ assigned' = assigned \cup {o8}

Next ==
  \/ AssignZenon
  \/ AssignIsabelle
  \/ AssignCVC3
  \/ AssignYices
  \/ AssignVeriT
  \/ AssignZ3
  \/ AssignSPASS
  \/ AssignLS4

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(AssignZenon)
  /\ WF_vars(AssignIsabelle)
  /\ WF_vars(AssignCVC3)
  /\ WF_vars(AssignYices)
  /\ WF_vars(AssignVeriT)
  /\ WF_vars(AssignZ3)
  /\ WF_vars(AssignSPASS)
  /\ WF_vars(AssignLS4)

EXTENSION ==
  \A A, B \in SUBSET PROBLEMS :
    (\A x \in A : x \in B) /\ (\A x \in B : x \in A) => A = B

NOSET ==
  \A x \in PROBLEMS : TRUE

====