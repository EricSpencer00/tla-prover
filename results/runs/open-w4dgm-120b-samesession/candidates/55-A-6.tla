---- MODULE MCEcho ----
EXTENDS Naturals
CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node

VARIABLES status, parent, reply, echoMsg, reached

vars == <<status, parent, reply, echoMsg, reached>>

TypeOK ==
  /\ status \in [Node -> {"up", "down"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ reply \in [Node -> {"none", "echo", "done"}]
  /\ echoMsg \in [Node -> 0..Cardinality(Node)]
  /\ reached \subseteq Node

\* A node is an ancestor of itself, and the echo counts reaching a node
\* and that node naming it as parent must agree, so a node never hears
\* itself reflected back through a loop.
AncestorProperties ==
  /\ \A n \in Node : initiator \in ancestorsOf[n]
  /\ \A n \in Node : initiator \in ancestorsOf[n] => initiator \in ancestorsOf[initiator]
  /\ \A m, n \in Node : initiator \in ancestorsOf[n] /\ n \in ancestorsOf[m] => initiator \in ancestorsOf[m]

\* The ancestor-of delegate relation is computed from the parent relation.
AncestorsOf(n) == {n} \cup (IF parent[n] = NoNode THEN {} ELSE AncestorsOf(parent[n]))

Init ==
  /\ status = [n \in Node |-> "up"]
  /\ parent = [n \in Node |-> NoNode]
  /\ reply = [n \in Node |-> "none"]
  /\ echoMsg = [n \in Node |-> 0]
  /\ reached = {}

StartEcho ==
  /\ status[initiator] = "up"
  /\ parent[initiator] = NoNode
  /\ status' = [status EXCEPT ![initiator] = "down"]
  /\ reached' = reached \cup {initiator}
  /\ UNCHANGED <<parent, reply, echoMsg>>

SendAck(m, n) ==
  /\ status[m] = "up"
  /\ <<m, n>> \in R
  /\ n \notin reached
  /\ status' = [status EXCEPT ![n] = "down"]
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ reached' = reached \cup {n}
  /\ UNCHANGED <<reply, echoMsg>>

EmitEcho(n) ==
  /\ status[n] = "down"
  /\ parent[n] # NoNode
  /\ reply[n] = "none"
  /\ reply' = [reply EXCEPT ![n] = "echo"]
  /\ echoMsg' = [echoMsg EXCEPT ![parent[n]] = @ + 1]
  /\ UNCHANGED <<status, parent, reached>>

CompleteEcho(n) ==
  /\ reply[n] = "echo"
  /\ status[n] = "down"
  /\ reply' = [reply EXCEPT ![n] = "done"]
  /\ UNCHANGED <<status, parent, echoMsg, reached>>

\* The initiator never sends an echo of its own because it has no parent.
EmitEchoForInitiator == EmitEcho(initiator) \/ UNCHANGED vars

Next ==
  \/ StartEcho
  \/ \E m \in Node, n \in Node : SendAck(m, n)
  \/ \E n \in Node : EmitEcho(n)
  \/ \E n \in Node : CompleteEcho(n)

Spec == Init /\ [][Next]_vars

PrintAdjacency ==
  /\ status \in [Node -> {"up", "down"}]
  /\ UNCHANGED vars
  /\ \E n \in Node : n = n
====