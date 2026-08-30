---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sent, received, answered

vars == <<parent, sent, received, answered>>

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ sent = {}
  /\ received = {}
  /\ answered = {}

SendEcho(m, n) ==
  /\ n \in Node
  /\ m \in Node
  /\ n # m
  /\ <<n, m>> \notin sent
  /\ sent' = sent \cup {<<n, m>>}
  /\ UNCHANGED <<parent, received, answered>>

ReceiveEcho(n, m) ==
  /\ <<n, m>> \in sent
  /\ <<n, m>> \notin received
  /\ received' = received \cup {<<n, m>>}
  /\ UNCHANGED <<parent, sent, answered>>

Adopt(n, m) ==
  /\ <<n, m>> \in received
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ UNCHANGED <<sent, received, answered>>

Answer(n, m) ==
  /\ parent[n] = m
  /\ n \in R
  /\ <<n, m>> \notin answered
  /\ answered' = answered \cup {<<n, m>>}
  /\ UNCHANGED <<parent, sent, received>>

Rest ==
  /\ \A n \in Node : parent[n] # NoNode
  /\ \A n \in Node : (n \in R) => (parent[n] \in R)
  /\ \A n1, n2 \in Node : (parent[n1] = n2) => (parent[n2] \in {n1, NoNode})
  /\ UNCHANGED vars

Next ==
  \/ \E m \in Node, n \in Node : SendEcho(m, n)
  \/ \E n \in Node, m \in Node : ReceiveEcho(n, m)
  \/ \E n \in Node, m \in Node : Adopt(n, m)
  \/ \E n \in Node, m \in Node : Answer(n, m)
  \/ Rest

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ sent \subseteq (Node \X Node)
  /\ received \subseteq (Node \X Node)
  /\ answered \subseteq (Node \X Node)

AncestorProperties ==
  /\ \A n \in Node : (n # initiator) => (parent[n] # NoNode)
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] \in {n, NoNode})
  /\ \A n \in Node : (n # initiator) => (parent[n] \in R)
  /\ \A n \in Node : (n \in R) => (parent[n] \in R)

TestSpec == Spec /\ TypeOK /\ AncestorProperties
====