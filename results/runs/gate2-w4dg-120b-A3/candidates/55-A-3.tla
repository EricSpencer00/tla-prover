---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, ackCount, active

vars == <<parent, ackCount, active>>

N1 == Node
I1 == initiator
R1 == R

Init ==
  /\ parent = [v \in Node |-> NoNode]
  /\ ackCount = [v \in Node |-> 0]
  /\ active = initiator

SendEcho(v) ==
  /\ v \in R
  /\ parent[v] = NoNode
  /\ v # initiator
  /\ parent' = [parent EXCEPT ![v] = initiator]
  /\ active' = IF initiator \in R THEN initiator ELSE v
  /\ ackCount' = [ackCount EXCEPT ![initiator] = ackCount[initiator] + 1]

SendTree(v) ==
  /\ v \in R
  /\ parent[v] = NoNode
  /\ v # initiator
  /\ \E u \in Node : u # v /\ u \in R /\ parent' = [parent EXCEPT ![v] = u]
  /\ active' = IF initiator \in R THEN initiator ELSE v
  /\ ackCount' = [ackCount EXCEPT ![u] = ackCount[u] + 1]

Acknowledge(v) ==
  /\ parent[v] # NoNode
  /\ v # initiator
  /\ ackCount' = [ackCount EXCEPT ![parent[v]] = ackCount[parent[v]] + 1]
  /\ active' = parent[v]
  /\ UNCHANGED parent

Idle ==
  /\ active = NoNode
  /\ UNCHANGED vars

Next ==
  \/ \E v \in Node : SendEcho(v)
  \/ \E v \in Node : SendTree(v)
  \/ \E v \in Node : Acknowledge(v)
  \/ Idle

Spec ==
  /\ Spec == Init /\ [][Next]_vars
  /\ WF_vars(Idle)

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ ackCount \in [Node -> Nat]
  /\ active \in Node \cup {NoNode}

AncestorProperties ==
  /\ \A v \in Node : initiator \in {w \in Node : w = v \/ w \in {parent[w] : w \in Node}}
  /\ \A v \in Node : (v # initiator) => (parent[v] # v)
  /\ \A v \in Node :
       ~(\E k \in Nat : k > 0 /\ v \in {parent[p] : p \in {parent[w] : w \in {parent[w] : w \in Node | k - 1}}})

TestSpec ==
  /\ Spec
  /\ UNCHANGED vars

====