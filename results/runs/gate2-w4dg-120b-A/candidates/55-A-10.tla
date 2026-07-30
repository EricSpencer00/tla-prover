---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME R \subseteq [Node \X Node]

VARIABLES init, parent, parentPort, acked, active, m

vars == <<init, parent, parentPort, acked, active, m>>

RECURSIVE Reachable(_)
Reachable(n) ==
  \/ n = initiator
  \/ \E x \in Node : Reachable(x) /\ parent[x] = n

TypeOK ==
  /\ init \in Node
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ parentPort \in [Node -> Node \cup {NoNode}]
  /\ acked \subseteq Node
  /\ active \subseteq Node
  /\ m \in [Node -> 0..4]

AncestorProperties ==
  /\ \A n \in Node : init = initiator => Reachable(n)
  /\ \A n \in Node : n \in acked => Reachable(n)

Init ==
  /\ init = initiator
  /\ parent = [n \in Node |-> NoNode]
  /\ parentPort = [n \in Node |-> NoNode]
  /\ acked = {}
  /\ active = {initiator}
  /\ m = [n \in Node |-> 0]

SendEcho(n, c) ==
  /\ n \in active
  /\ c \in Node
  /\ c # n
  /\ <<n, c>> \in R
  /\ parent[c] = NoNode
  /\ parent' = [parent EXCEPT ![c] = n]
  /\ parentPort' = [parentPort EXCEPT ![c] = n]
  /\ active' = active \cup {c}
  /\ UNCHANGED <<init, acked, m>>

SendAck(c) ==
  /\ c \in active
  /\ parent[c] # NoNode
  /\ parentPort[parent[c]] = c
  /\ m[c] < 4
  /\ m' = [m EXCEPT ![c] = m[c] + 1]
  /\ acked' = acked \cup {c}
  /\ active' = active \ {c}
  /\ UNCHANGED <<init, parent, parentPort>>

EchoPass ==
  \/ \E n \in Node, c \in Node : SendEcho(n, c)
  \/ \E c \in Node : SendAck(c)

TestSpec == EchoPass

Next == EchoPass

Spec == Init /\ [][Next]_vars

====