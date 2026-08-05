---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

\* Echo spanning-tree, modelled on a concrete three-node fully-connected graph
\* so the full reachable state space can be explored exhaustively.
Node == {"n1", "n2", "n3"}
R == {[n1 |-> "n1", n2 |-> "n2", n3 |-> "n3"]} \cup
     {[n1 |-> "n1", n2 |-> "n2", n3 |-> "n3"]} \cup
     {[n1 |-> "n1", n2 |-> "n2", n3 |-> "n3"]} \cup
     {[n1 |-> "n1", n2 |-> "n2", n3 |-> "n3"]} \cup
     {[n1 |-> "n1", n2 |-> "n2", n3 |-> "n3"]} \cup
     {[n1 |-> "n1", n2 |-> "n2", n3 |-> "n3"]}
NoNode == "NoNode"
initiator == "n1"

VARIABLES phase, parent, recvBy, sent

TypeOK ==
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ recvBy \in [Node -> SUBSET Node]
  /\ sent \in SUBSET Node

\* The initiator is the only node that may start the broadcast.
Init ==
  /\ phase = [n \in Node |-> IF n = initiator THEN "active" ELSE "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ recvBy = [n \in Node |-> {}]
  /\ sent = {}

\* A node forwards the broadcast to every other node it is connected to.
Push ==
  /\ \E n \in Node :
       /\ phase[n] = "active"
       /\ \E m \in Node :
            /\ n # m
            /\ recvBy' = [recvBy EXCEPT ![m] = @ \cup {n}]
       /\ sent' = sent \cup {n}
  /\ UNCHANGED <<phase, parent>>

\* A node that receives a broadcast for the first time activates and records
\* its ancestor as the sender that reached it.
Receive ==
  /\ \E n \in Node :
       /\ phase[n] = "idle"
       /\ \E m \in recvBy[n] :
            /\ phase' = [phase EXCEPT ![n] = "active"]
            /\ parent' = [parent EXCEPT ![n] = m]
  /\ UNCHANGED <<recvBy, sent>>

\* A node that has collected a response from every other node is done.
Done ==
  /\ \E n \in Node :
       /\ phase[n] = "active"
       /\ sent = Node \ {n}
       /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, recvBy, sent>>

\* The initiator completes once it is done and has collected all other
\* nodes' broadcasts as well.
InitiatorDone ==
  /\ phase[initiator] = "active"
  /\ sent = Node
  /\ phase' = [phase EXCEPT ![initiator] = "done"]
  /\ UNCHANGED <<parent, recvBy, sent>>

Next == Push \/ Receive \/ Done \/ InitiatorDone

vars == <<phase, parent, recvBy, sent>>

Spec == Init /\ [][Next]_vars

\* Under the spanning-tree protocol, every other node is an ancestor of the
\* initiator, and no node is an ancestor of itself, so the ancestor
\* relation is acyclic and rooted at the initiator.
AncestorProperties ==
  /\ \A n \in Node : n # initiator => n \in {m \in Node : parent[m] = n}
  /\ \A n \in Node : n \in {m \in Node : parent[m] = n} => n = initiator

TestSpec == Spec /\ TRUE

====