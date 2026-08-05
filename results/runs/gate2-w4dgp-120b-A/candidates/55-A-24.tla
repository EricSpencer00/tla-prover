---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, acked, phase

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ acked \subseteq Node
  /\ phase \in [Node -> {"init", "active", "done"}]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ acked = {}
  /\ phase = [n \in Node |-> "init"]

InitFrom(n) ==
  /\ phase[n] = "init"
  /\ \E m \in Node : <<n, m>> \in R /\ phase[m] = "init" /\ phase' = [phase EXCEPT ![m] = "active"]
  /\ UNCHANGED <<parent, acked>>

Send(n) ==
  /\ phase[n] = "active"
  /\ \E m \in Node : <<n, m>> \in R /\ phase[m] = "init" /\ phase' = [phase EXCEPT ![m] = "active"]
  /\ UNCHANGED <<parent, acked>>

Ack(n, m) ==
  /\ phase[n] = "active"
  /\ parent[m] = NoNode
  /\ phase[m] = "active"
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ acked' = acked \cup {m}
  /\ UNCHANGED phase

Done(n) ==
  /\ phase[n] = "active"
  /\ \A m \in Node : parent[m] = n => m \in acked
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, acked>>

Next ==
  \/ \E n \in Node : InitFrom(n) \/ Send(n) \/ Done(n)
  \/ \E n \in Node, m \in Node : Ack(n, m)

TestSpec == Init /\ [][Next]_<<parent, acked, phase>>

AncestorProperties ==
  /\ parent[initiator] = NoNode
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A n \in Node \ {initiator} : initiator \in (parent)^[*][n]

====