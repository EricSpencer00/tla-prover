---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ProcSet == 1..N

\* ----------------------------------------------------------------------
\* State variables (same as the original Boulanger specification)
\* ----------------------------------------------------------------------
VARIABLES pc,          \* program counter for each process
          ticket,      \* ticket number for each process
          sharedVar    \* a placeholder for the shared resource (e.g., a lock)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of possible program counter locations
PCStates == {"idle", "request", "wait", "critical", "exit"}

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [i \in ProcSet |-> "idle"]
  /\ ticket = [i \in ProcSet |-> 0]
  /\ sharedVar = FALSE
  /\ Nat = 0..MaxNat

\* ----------------------------------------------------------------------
\* Actions (same as in the original Boulanger specification)
\* ----------------------------------------------------------------------
Idle(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "request"]
  /\ UNCHANGED <<ticket, sharedVar>>

Request(i) ==
  /\ pc[i] = "request"
  /\ ticket' = [ticket EXCEPT ![i] = Max({ticket[j] : j \in ProcSet}) + 1]
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED sharedVar

Wait(i) ==
  /\ pc[i] = "wait"
  /\ \A j \in ProcSet :
        (j # i) => (ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<ticket, sharedVar>>

Critical(i) ==
  /\ pc[i] = "critical"
  /\ sharedVar = FALSE
  /\ sharedVar' = TRUE
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED ticket

Exit(i) ==
  /\ pc[i] = "exit"
  /\ sharedVar = TRUE
  /\ sharedVar' = FALSE
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED ticket

Next ==
  \E i \in ProcSet :
    \/ Idle(i)
    \/ Request(i)
    \/ Wait(i)
    \/ Critical(i)
    \/ Exit(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket, sharedVar>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion ==
  \A i, j \in ProcSet :
    (i # j) => ~(pc[i] = "critical" /\ pc[j] = "critical")

TypeOK ==
  /\ pc \in [ProcSet -> PCStates]
  /\ ticket \in [ProcSet -> Nat]
  /\ sharedVar \in BOOLEAN

Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* Liveness properties (none specified)
\* ----------------------------------------------------------------------
\* (No liveness property is defined as per the description.)

\* ----------------------------------------------------------------------
\* State constraint to keep ticket numbers below MaxNat
\* ----------------------------------------------------------------------
StateConstraint ==
  \A i \in ProcSet : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* The model checker will use Spec as the specification,
\* and the following invariants are required:
\*   MutualExclusion, TypeOK, Inv
\* ----------------------------------------------------------------------
====