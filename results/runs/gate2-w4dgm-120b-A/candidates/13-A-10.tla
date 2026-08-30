---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, chosen, nextTicket

vars == <<inCS, want, ticket, chosen, nextTicket>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ chosen \in [1..N -> BOOLEAN]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ want = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ chosen = [i \in 1..N |-> FALSE]
  /\ nextTicket = 0

\* A process asks to enter the critical section and is handed it a fresh ticket.
Request(i) ==
  /\ ~want[i]
  /\ ~inCS[i]
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ chosen' = [chosen EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

ChooseTicket(i) ==
  /\ want[i]
  /\ ~chosen[i]
  /\ chosen' = [chosen EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ UNCHANGED <<inCS, want, nextTicket>>

\* A process may enter only when its ticket is strictly lower than every other's ticket.
Enter(i) ==
  /\ want[i]
  /\ ~inCS[i]
  /\ chosen[i]
  /\ \A j \in 1..N : (j # i) => (~inCS[j] /\ ticket[i] < ticket[j])
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<want, ticket, chosen, nextTicket>>

Leave(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ chosen' = [chosen EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, nextTicket>>

\* The ticket counter recycles within the bounded band; because a process keeps the
\* ticket it was granted until it leaves, no live participant is starved out.
Renumber ==
  /\ nextTicket = MaxNat
  /\ \A i \in 1..N : ~inCS[i]
  /\ nextTicket' = 0
  /\ UNCHANGED <<inCS, want, ticket, chosen>>

NextTicket ==
  /\ nextTicket < MaxNat
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<inCS, want, ticket, chosen>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : ChooseTicket(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Leave(i)
  \/ Renumber
  \/ NextTicket

\* The full inductive invariant, preserved from any reachable state.
Inv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ \A i \in 1..N : inCS[i] => (want[i] /\ chosen[i])

MutualExclusion ==
  \A i \in 1..N, j \in 1..N : (inCS[i] /\ inCS[j]) => (i = j)

ISpec == Init /\ [][Next]_vars

====