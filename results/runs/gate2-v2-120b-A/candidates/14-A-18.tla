---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N
NatSet == Nat

\* ----------------------------------------------------------------------
\* State variables (inherited from Boulanger)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The finite set of natural numbers (0..MaxNat) is identified with Nat
NatDef == Nat = 0..MaxNat

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ NatDef
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]

\* ----------------------------------------------------------------------
\* Actions (inherited from Boulanger, simplified for illustration)
\* ----------------------------------------------------------------------
Enter(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = Max(ticket) + 1]
  /\ ticket[i] = Max(ticket) + 1
  /\ UNCHANGED <<>>

Acquire(i) ==
  /\ i \in Proc
  /\ pc[i] = "waiting"
  /\ \A j \in Proc :
        (j # i) => ( (pc[j] # "critical") \/ (ticket[i] < ticket[j]) )
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED ticket

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in Proc: Enter(i)
  \/ \E i \in Proc: Acquire(i)
  \/ \E i \in Proc: Exit(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket>>

\* ----------------------------------------------------------------------
\* Type correctness predicate (type invariant)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"idle", "waiting", "critical"}]
  /\ ticket \in [Proc -> NatSet]
  /\ \A i \in Proc: ticket[i] \in NatSet

\* ----------------------------------------------------------------------
\* Mutual exclusion invariant
\* ----------------------------------------------------------------------
MutualExclusion ==
  \A i, j \in Proc : (i # j) => ~ (pc[i] = "critical" /\ pc[j] = "critical")

\* ----------------------------------------------------------------------
\* Full inductive invariant (combination of safety properties)
\* ----------------------------------------------------------------------
Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* State constraint: ticket numbers must stay strictly below MaxNat
\* ----------------------------------------------------------------------
StateConstraint ==
  \A i \in Proc : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* The initialization also respects the state constraint
\* ----------------------------------------------------------------------
InitWithConstraint == Init /\ StateConstraint

\* ----------------------------------------------------------------------
\* The specification used for model checking includes the constraint
\* ----------------------------------------------------------------------
Spec == InitWithConstraint /\ [][Next]_<<pc, ticket>>

====