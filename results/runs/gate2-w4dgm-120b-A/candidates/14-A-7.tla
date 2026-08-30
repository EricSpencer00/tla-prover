---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, MaxNat

VARIABLES holder, inCS, ticket, request, clock
vars == <<holder, inCS, ticket, request, clock>>

Nodes == 0..(N - 1)
Succ(n) == (n + 1) % N

TypeOK ==
  /\ holder \in Nodes
  /\ inCS \in [Nodes -> BOOLEAN]
  /\ ticket \in [Nodes -> 0..MaxNat]
  /\ request \in [Nodes -> 0..MaxNat]
  /\ clock \in 0..MaxNat

Init ==
  /\ holder = 0
  /\ inCS = [n \in Nodes |-> FALSE]
  /\ ticket = [n \in Nodes |-> 0]
  /\ request = [n \in Nodes |-> 0]
  /\ clock = 0

Request(n) ==
  /\ ~inCS[n]
  /\ request[n] < clock
  /\ request' = [request EXCEPT ![n] = clock]
  /\ UNCHANGED <<holder, inCS, ticket, clock>>

Enter(n) ==
  /\ holder = n
  /\ request[n] > ticket[n]
  /\ ~inCS[n]
  /\ inCS' = [inCS EXCEPT ![n] = TRUE]
  /\ ticket' = [ticket EXCEPT ![n] = request[n]]
  /\ UNCHANGED <<holder, request, clock>>

Exit(n) ==
  /\ inCS[n]
  /\ inCS' = [inCS EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<holder, ticket, request, clock>>

PassToken ==
  /\ \A n \in Nodes: ~inCS[n]
  /\ holder' = Succ(holder)
  /\ UNCHANGED <<inCS, ticket, request, clock>>

Tick ==
  /\ clock < MaxNat
  /\ clock' = clock + 1
  /\ UNCHANGED <<holder, inCS, ticket, request>>

Next ==
  \/ \E n \in Nodes: Request(n)
  \/ \E n \in Nodes: Enter(n)
  \/ \E n \in Nodes: Exit(n)
  \/ PassToken
  \/ Tick

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A m, n \in Nodes: (inCS[m] /\ inCS[n]) => (m = n)

Inv ==
  / \A n \in Nodes: inCS[n] => (holder = n /\ ticket[n] = request[n])
  /\ \A n \in Nodes: inCS[n] => ticket[n] <= request[n]
  /\ \A n \in Nodes: ~inCS[n] => ticket[n] <= request[n]

StateConstraint == \A n \in Nodes: ticket[n] < MaxNat

====