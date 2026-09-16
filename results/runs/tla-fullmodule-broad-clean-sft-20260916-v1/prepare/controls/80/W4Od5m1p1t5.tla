---- MODULE W4Od5m1p1t5 ----
EXTENDS Naturals
CONSTANTS Players, Delta, MaxVer
ASSUME Delta \in Nat /\ MaxVer \in Nat
VARIABLES holder, record, version, contrib, staged

vars == <<holder, record, version, contrib, staged>>

RECURSIVE SumFn(_)
SumFn(S) == IF S = {} THEN 0
            ELSE LET p == CHOOSE x \in S : TRUE
                 IN contrib[p] + SumFn(S \ {p})

Init ==
  /\ holder \in Players
  /\ record = 0
  /\ version = 0
  /\ contrib = [p \in Players |-> 0]
  /\ staged = [p \in Players |-> 0]

Stage(p) ==
  /\ holder = p
  /\ staged[p] = 0
  /\ version < MaxVer
  /\ staged' = [staged EXCEPT ![p] = Delta]
  /\ UNCHANGED <<holder, record, version, contrib>>

Commit(p) ==
  /\ holder = p
  /\ staged[p] > 0
  /\ record' = record + staged[p]
  /\ contrib' = [contrib EXCEPT ![p] = contrib[p] + staged[p]]
  /\ version' = version + 1
  /\ staged' = [staged EXCEPT ![p] = 0]
  /\ UNCHANGED holder

Advance(p) ==
  /\ holder = p
  /\ staged[p] = 0
  /\ \E q \in Players : holder' = q
  /\ UNCHANGED <<record, version, contrib, staged>>

AdminSeize ==
  /\ \E q \in Players : holder' = q
  /\ UNCHANGED <<record, version, contrib, staged>>

Next ==
  \/ \E p \in Players : Stage(p) \/ Commit(p) \/ Advance(p)
  \/ AdminSeize

Spec == Init /\ [][Next]_vars

NoLostUpdates == record = SumFn(Players)
====