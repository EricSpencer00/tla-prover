---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANT N, MaxNat, Nat

VARIABLES pc, ticket

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ProcSet == 1 .. N

\* ----------------------------------------------------------------------
\* State constraint (added as a variable definition to be used in Spec)
\* ----------------------------------------------------------------------
SC == \A i \in ProcSet: ticket[i] \in Nat /\ ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in ProcSet |-> "Idle"]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ SC

\* ----------------------------------------------------------------------
\* Actions (inherited from the Boulanger specification)
\* ----------------------------------------------------------------------
Request(i) ==
    /\ pc[i] = "Idle"
    /\ pc' = [pc EXCEPT ![i] = "Waiting"]
    /\ ticket' = [ticket EXCEPT ![i] = Max(ticket) + 1]
    /\ ticket'[i] < MaxNat
    /\ UNCHANGED << >>

Enter(i) ==
    /\ pc[i] = "Waiting"
    /\ \A j \in ProcSet :
          (j # i) => (pc[j] # "CS" /\ ticket[i] < ticket[j] \/ ticket[i] = ticket[j] /\ i < j)
    /\ pc' = [pc EXCEPT ![i] = "CS"]
    /\ UNCHANGED ticket

Exit(i) ==
    /\ pc[i] = "CS"
    /\ pc' = [pc EXCEPT ![i] = "Idle"]
    /\ UNCHANGED ticket

Next ==
    \/ \E i \in ProcSet: Request(i)
    \/ \E i \in ProcSet: Enter(i)
    \/ \E i \in ProcSet: Exit(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket>>

\* ----------------------------------------------------------------------
\* Invariant definitions (same as Boulanger)
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in ProcSet :
        (i # j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

TypeOK ==
    /\ pc \in [ProcSet -> {"Idle", "Waiting", "CS"}]
    /\ ticket \in [ProcSet -> Nat]

Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* Theorems (optional, to expose the required identifiers)
\* ----------------------------------------------------------------------
THEOREM Spec == Spec
THEOREM MutualExclusion == MutualExclusion
THEOREM TypeOK == TypeOK
THEOREM Inv == Inv

====