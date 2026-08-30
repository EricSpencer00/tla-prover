---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES shared, ticket, inCS, auth, crashed
vars == <<shared, ticket, inCS, auth, crashed>>

Init ==
  /\ shared = 0
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ auth = [p \in 1..N |-> FALSE]
  /\ crashed = {}

Request(p) ==
  /\ p \notin crashed
  /\ ticket[p] = 0
  /\ shared = 0
  /\ shared' = shared + 1
  /\ ticket' = [ticket EXCEPT ![p] = shared + 1]
  /\ UNCHANGED <<inCS, auth, crashed>>

Enter(p) ==
  /\ p \notin crashed
  /\ auth[p] = FALSE
  /\ ticket[p] > 0
  /\ inCS[p] = FALSE
  /\ \A q \in 1..N : inCS[q] = FALSE
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ auth' = [auth EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<shared, ticket, crashed>>

Exit(p) ==
  /\ inCS[p] = TRUE
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ auth' = [auth EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED <<shared, crashed>>

Crash(p) ==
  /\ p \notin crashed
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED <<shared, ticket, inCS, auth>>

Recover(p) ==
  /\ p \in crashed
  /\ crashed' = crashed \ {p}
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ auth' = [auth EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ UNCHANGED shared

Idle == UNCHANGED vars

Next ==
  \/ Idle
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)
  \/ \E p \in 1..N : Crash(p)
  \/ \E p \in 1..N : Recover(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 1..N : inCS[p] = TRUE => (\A q \in 1..N : q # p => inCS[q] = FALSE)

TypeOK ==
  /\ shared \in 0..MaxNat
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ auth \in [1..N -> BOOLEAN]
  /\ crashed \subseteq 1..N

TicketBound == \A p \in 1..N : ticket[p] <= MaxNat

Inv == MutualExclusion /\ TypeOK /\ TicketBound

NatOverride == Nat
====