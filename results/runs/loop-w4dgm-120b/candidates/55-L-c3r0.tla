---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node

VARIABLES parent, acked, waiting, phase

vars == <<parent, acked, waiting, phase>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ acked \in [Node -> BOOLEAN]
  /\ waiting \subseteq Node
  /\ phase \in {"idle", "echoing"}

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ acked = [n \in Node |-> FALSE]
  /\ waiting = {initiator}
  /\ phase = "idle"

\* Initiation is gated on the current phase; the irreversibility is exactly
\* that gate -- once phase = "echoing" no node may re-enter waiting.
StartEcho ==
  /\ phase = "idle"
  /\ waiting' = {initiator}
  /\ phase' = "echoing"
  /\ UNCHANGED <<parent, acked>>

SendEcho(n, m) ==
  /\ n \in waiting
  /\ m \in R
  /\ m # n
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ waiting' = waiting \cup {m}
  /\ UNCHANGED <<acked, phase>>

Ack(n) ==
  /\ n \in waiting
  /\ waiting' = waiting \ {n}
  /\ acked' = [acked EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, phase>>

Quiesce ==
  /\ phase = "echoing"
  /\ waiting = {}
  /\ phase' = "idle"
  /\ UNCHANGED <<parent, acked, waiting>>

Next ==
  \/ StartEcho
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E n \in Node : Ack(n)
  \/ Quiesce

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ (acknowledgedNonRoot == {n \in Node : acked[n] /\ n # initiator})
  /\ (acknowledgedNonRoot \subseteq {n \in Node : parent[n] # NoNode})
  /\ \A n \in Node : (acked[n] /\ n # initiator) => (parent[n] # NoNode)
  /\ \A n \in Node : (parent[n] # NoNode) => (n # initiator)

TestSpec == Spec /\ AncestorProperties

====