---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* The Echo spanning tree algorithm, instantiated on a concrete three-node
\* fully-meshed graph for exhaustive model checking.  All state variables,
\* actions, and properties are inherited from the Echo spec; this module only
\* fixes the graph and the initiator.

VARIABLES parent, phase, echoCount, ackCount, active

vars == <<parent, phase, echoCount, ackCount, active>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ echoCount \in [Node -> 0..Cardinality(R)]
  /\ ackCount \in [Node -> 0..Cardinality(R)]
  /\ active \subseteq Node

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> "idle"]
  /\ echoCount = [n \in Node |-> 0]
  /\ ackCount = [n \in Node |-> 0]
  /\ active = {}

\* The initiator starts the spanning tree by broadcasting to every other node.
Start ==
  /\ phase[initiator] = "idle"
  /\ phase' = [phase EXCEPT ![initiator] = "active"]
  /\ active' = active \cup {initiator}
  /\ echoCount' = [echoCount EXCEPT ![initiator] = Cardinality(R)]
  /\ UNCHANGED <<parent, ackCount>>

\* A node that receives an echo adopts its sender as parent and becomes active.
Echo(n, m) ==
  /\ phase[n] = "idle"
  /\ m \in active
  /\ n # m
  /\ phase' = [phase EXCEPT ![n] = "active"]
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ active' = active \cup {n}
  /\ echoCount' = [echoCount EXCEPT ![n] = Cardinality(R)]
  /\ UNCHANGED ackCount

\* An active node acknowledges one echo it has not yet accounted for.
Ack(n) ==
  /\ phase[n] = "active"
  /\ ackCount[n] < echoCount[n]
  /\ ackCount' = [ackCount EXCEPT ![n] = @ + 1]
  /\ UNCHANGED <<parent, phase, echoCount, active>>

\* A node that has accounted for all its echoes marks itself done.
Done(n) ==
  /\ phase[n] = "active"
  /\ ackCount[n] = echoCount[n]
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, echoCount, ackCount, active>>

\* The initiator may re-broadcast while it is still active, refreshing its
\* echo count and resetting its acknowledgements.
Rebroadcast ==
  /\ phase[initiator] = "active"
  /\ echoCount' = [echoCount EXCEPT ![initiator] = Cardinality(R)]
  /\ ackCount' = [ackCount EXCEPT ![initiator] = 0]
  /\ UNCHANGED <<parent, phase, active>>

Next ==
  \/ Start
  \/ \E n \in Node, m \in Node : Echo(n, m)
  \/ \E n \in Node : Ack(n)
  \/ \E n \in Node : Done(n)
  \/ Rebroadcast

\* A test variant that prints the graph adjacency relation at startup.
TestSpec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node : (phase[n] = "done") => (initiator \in {n} \cup {parent[n]})
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[parent[n]] # n)

====