---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* Nat is overridden globally to a finite range in the .cfg file; the
\* operator below is the name the .cfg substitutes in for Nat.
NatOverride == Nat

VARIABLES inCS, number, choosing, ticket

vars == <<inCS, number, choosing, ticket>>

None == 0

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ number \in 0..MaxNat
  /\ choosing \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

MutualExclusion ==
  \A i \in 1..N, j \in 1..N : (inCS[i] /\ inCS[j]) => (i = j)

Inv ==
  /\ TypeOK
  /\ \A i \in 1..N : inCS[i] => number <= ticket[i]
  /\ \A i \in 1..N : ~inCS[i] => number < ticket[i]

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ number = 0
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]

Choose(i) ==
  /\ ~inCS[i]
  /\ ~choosing[i]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<inCS, number, ticket>>

AssignTicket(i) ==
  /\ choosing[i]
  /\ ticket' = [ticket EXCEPT ![i] = number + 1]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<inCS, number>>

Enter(i) ==
  /\ ~inCS[i]
  /\ ~choosing[i]
  /\ ticket[i] > number
  /\ \A j \in 1..N : ~inCS[j] => ticket[j] > ticket[i]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<number, choosing, ticket>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ number' = IF number < MaxNat THEN number + 1 ELSE number
  /\ UNCHANGED <<choosing, ticket>>

Next ==
  \/ \E i \in 1..N : Choose(i)
  \/ \E i \in 1..N : AssignTicket(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

ISpec == Init /\ [][Next]_vars

====