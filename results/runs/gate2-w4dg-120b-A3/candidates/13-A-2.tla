---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, act

vars == <<inCS, ticket, nextTicket, act>>

TypeOK ==
  /\ inCS \subseteq (1..N)
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ act \in [1..N -> {"idle", "waiting", "critical"}]

Init ==
  /\ inCS = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ act = [p \in 1..N |-> "idle"]

Request(p) ==
  /\ act[p] = "idle"
  /\ act' = [act EXCEPT ![p] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE MaxNat
  /\ UNCHANGED inCS

Enter(p) ==
  /\ act[p] = "waiting"
  /\ \A q \in 1..N : (q \in inCS) => (ticket[p] <= ticket[q])
  /\ act' = [act EXCEPT ![p] = "critical"]
  /\ inCS' = inCS \cup {p}
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
  /\ act[p] = "critical"
  /\ act' = [act EXCEPT ![p] = "idle"]
  /\ inCS' = inCS \ {p}
  /\ UNCHANGED <<ticket, nextTicket>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in inCS : p = q

Inv == TypeOK /\ MutualExclusion

NatOverride ==
  IF MaxNat < 0 THEN MaxNat ELSE MaxNat

====