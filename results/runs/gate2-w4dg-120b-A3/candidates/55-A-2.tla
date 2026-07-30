---- MODULE MCEcho ----
EXTENDS Naturals, TLC

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, done, echoCount, phase, acks

vars == <<parent, done, echoCount, phase, acks>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ done \in [Node -> BOOLEAN]
  /\ echoCount \in [Node -> 0..Cardinality(Node)]
  /\ phase \in [Node -> {"idle", "waiting", "done"}]
  /\ acks \subseteq Node

AncestorProperties ==
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => (parent[n] # initiator => parent[parent[n]] # NoNode)
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode)

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ done = [n \in Node |-> FALSE]
  /\ echoCount = [n \in Node |-> 0]
  /\ phase = [n \in Node |-> IF n = initiator THEN "waiting" ELSE "idle"]
  /\ acks = {}

SendEcho(n) ==
  /\ phase[n] = "idle"
  /\ phase' = [phase EXCEPT ![n] = "waiting"]
  /\ UNCHANGED <<parent, done, echoCount, acks>>

DeliverAck(n, m) ==
  /\ phase[n] = "waiting"
  /\ m \in Node
  /\ m # n
  /\ R[m, n]
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ echoCount' = [echoCount EXCEPT ![n] = echoCount[n] + 1]
  /\ acks' = acks \cup {n}
  /\ UNCHANGED done

AckDone(n) ==
  /\ phase[n] = "done"
  /\ done' = [done EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, echoCount, phase, acks>>

TestSpec == Init /\ [][\E n \in Node : SendEcho(n)]_vars

Next ==
  \/ \E n \in Node : SendEcho(n)
  \/ \E n \in Node, m \in Node : DeliverAck(n, m)
  \/ \E n \in Node : AckDone(n)

Spec == TestSpec

====