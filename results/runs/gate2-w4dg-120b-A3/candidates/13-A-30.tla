---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* NatOverride replaces the unbounded Nat from Naturals with a FINITE version
\* bounded by MaxNat, so the model's ticket numbers stay within a checkable range.
NatOverride == (0 .. MaxNat)

VARIABLES tickets, inCS, choosing

vars == <<tickets, inCS, choosing>>

TypeOK ==
  /\ tickets \in [1..N -> NatOverride]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ choosing \in [1..N -> BOOLEAN]

\* The inductive invariant is the same as the bakery spec's: a process is in its
\* critical section only while its ticket is strictly lower than every other
\* process's ticket.
Inv ==
  /\ TypeOK
  /\ \A i \in 1..N : inCS[i] => (\A j \in 1..N : tickets[i] < tickets[j])

Init ==
  /\ tickets = [i \in 1..N |-> 0]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ choosing = [i \in 1..N |-> FALSE]

Choose(i) ==
  /\ ~inCS[i]
  /\ ~choosing[i]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ tickets' = [tickets EXCEPT ![i] = IF \E j \in 1..N : tickets[j] > tickets[i] /\ tickets[j] < MaxNat
                                   THEN tickets[i] + 1 ELSE tickets[i]]
  /\ UNCHANGED inCS

Enter(i) ==
  /\ choosing[i]
  /\ \A j \in 1..N : i = j \/ tickets[i] < tickets[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED tickets

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ tickets' = [tickets EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Next ==
  \/ \E i \in 1..N : Choose(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

ISpec == Init /\ [][Next]_vars

MutualExclusion == \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => (i = j)

====