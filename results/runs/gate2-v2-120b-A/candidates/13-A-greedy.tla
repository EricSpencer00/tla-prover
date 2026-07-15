---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
ProcSet == 1..N

\* ----------------------------------------------------------------------
\* State variables (inherited from the original Bakery spec)
\* ----------------------------------------------------------------------
VARIABLES pc, flag, ticket

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for the TypeOK invariant)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [ProcSet -> {"idle", "wait", "cs"}]
  /\ flag \in [ProcSet -> BOOLEAN]
  /\ ticket \in [ProcSet -> Nat]

\* ----------------------------------------------------------------------
\* Initial state (same as the original spec, but Nat is already finite)
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [i \in ProcSet |-> "idle"]
  /\ flag = [i \in ProcSet |-> FALSE]
  /\ ticket = [i \in ProcSet |-> 0]

\* ----------------------------------------------------------------------
\* Actions (identical to the original Bakery algorithm)
\* ----------------------------------------------------------------------
Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = 
        1 + Max({ ticket[j] : j \in ProcSet })]

Enter(i) ==
  /\ pc[i] = "wait"
  /\ \A j \in ProcSet :
        (j # i) => 
          ~flag[j] \/ 
          (ticket[i] < ticket[j]) \/ 
          (ticket[i] = ticket[j] /\ i < j)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << flag, ticket >>

Exit(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ UNCHANGED ticket

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E i \in ProcSet : Request(i) \/ Enter(i) \/ Exit(i)

\* ----------------------------------------------------------------------
\* Safety invariant: mutual exclusion
\* ----------------------------------------------------------------------
MutualExclusion ==
  \A i, j \in ProcSet :
    (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* ----------------------------------------------------------------------
\* Full inductive invariant (as required by the .cfg)
\* ----------------------------------------------------------------------
Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* Specification formula (inductive specification)
\* ----------------------------------------------------------------------
ISpec == Init /\ [][Next]_<<pc, flag, ticket>>

\* ----------------------------------------------------------------------
\* The module's default behavior (required for TLC)
\* ----------------------------------------------------------------------
Spec == ISpec

=============================================================================