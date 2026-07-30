---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, target

vars == <<inCS, ticket, nextTicket, target>>

TypeOK ==
  /\ inCS \in SUBSET (1..N)
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ target \in 1..N

Init ==
  /\ inCS = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ target = 1

Request(p) ==
  /\ p \notin inCS
  /\ ticket[p] = 0
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket + 1]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<inCS, target>>

Enter(p) ==
  /\ p \notin inCS
  /\ ticket[p] > 0
  /\ target = p
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED <<ticket, nextTicket, target>>

Leave(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ target' = (p % N) + 1
  /\ UNCHANGED <<ticket, nextTicket>>

Pass ==
  /\ \E p \in 1..N : Request(p)
  /\ \E p \in 1..N : Enter(p)
  /\ \E p \in 1..N : Leave(p)

Next == Pass

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in 1..N : (p \in inCS /\ q \in inCS) => p = q

Inv ==
  /\ TypeOK
  /\ \A p \in inCS : ticket[p] > 0

StateBound == \A p \in 1..N : ticket[p] < MaxNat

====