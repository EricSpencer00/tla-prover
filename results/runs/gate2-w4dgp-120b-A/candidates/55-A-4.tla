---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, received, acked, leader

vars == <<parent, received, acked, leader>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ received \subseteq (Node \X Node)
  /\ acked \subseteq (Node \X Node)
  /\ leader \in Node

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ received = {}
  /\ acked = {}
  /\ leader = initiator

ReceiveEcho ==
  /\ \E u, v \in Node :
       /\ u # v
       /\ <<u, v>> \notin received
       /\ <<v, u>> \notin acked
       /\ received' = received \cup {<<u, v>>}
  /\ UNCHANGED <<parent, acked, leader>>

SendAck ==
  /\ \E u, v \in Node :
       /\ <<u, v>> \in received
       /\ <<u, v>> \notin acked
       /\ acked' = acked \cup {<<u, v>>}
  /\ UNCHANGED <<parent, received, leader>>

ParentOf ==
  \E n \in Node :
    /\ \E m \in Node :
         /\ <<m, n>> \in acked
         /\ parent[n] = NoNode
         /\ parent' = [parent EXCEPT ![n] = m]
    /\ UNCHANGED <<received, acked, leader>>

SetLeader ==
  /\ \E n \in Node :
       /\ parent[n] # NoNode
       /\ leader' = n
  /\ UNCHANGED <<parent, received, acked>>

Next ==
  \/ ReceiveEcho
  \/ SendAck
  \/ ParentOf
  \/ SetLeader

Spec == Init /\ [][Next]_vars

PrintGraph ==
  /\ \E t \in 1..2 : TRUE
  /\ UNCHANGED vars

TestSpec == Spec \/ PrintGraph

AncestorProperties ==
  /\ (leader # initiator) => (parent[leader] = initiator)
  /\ (parent[initiator] = NoNode)
  /\ \A x \in Node : (x # initiator /\ parent[x] # NoNode) => parent[parent[x]] # NoNode

====