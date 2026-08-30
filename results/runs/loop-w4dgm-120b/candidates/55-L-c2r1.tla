---- MODULE MCEcho ----
\* Model-checking configuration for the Echo spanning-tree algorithm.
\* This module inherits the full action set from the Echo specification
\* and instantiates its constants with a small, fully-connected 3-node graph.
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES phase, treeParent, treeReady, ackedReady

Vars == << phase, treeParent, treeReady, ackedReady >>

\* Echo messages are held in a set (multiset) and delivered in any order.
Message == [src : Node, dst : Node, kind : {"tree", "ready"}]
Messages == SUBSET Message

RECURSIVE Anc(n)
Anc(n) == IF n = initiator THEN "root"
         ELSE IF treeParent[n] = NoNode THEN "none"
         ELSE treeParent[n] # initiator /\ Anc(treeParent[n])

TypeOK ==
  /\ phase \in [Node -> {"init", "tree", "ready", "done"}]
  /\ treeParent \in [Node -> Node \cup {NoNode}]
  /\ treeReady \in [Node -> BOOLEAN]
  /\ ackedReady \in [Node -> BOOLEAN]

Init ==
  /\ phase = [n \in Node |-> "init"]
  /\ treeParent = [n \in Node |-> NoNode]
  /\ treeReady = [n \in Node |-> FALSE]
  /\ ackedReady = [n \in Node |-> FALSE]

StartTree(n) ==
  /\ n \in R
  /\ n # initiator
  /\ phase[initiator] = "init"
  /\ phase' = [phase EXCEPT ![initiator] = "tree"]
  /\ treeParent' = [treeParent EXCEPT ![initiator] = NoNode]
  /\ UNCHANGED << treeReady, ackedReady >>

DeliverTree(m) ==
  /\ m.kind = "tree"
  /\ phase[m.dst] = "init"
  /\ phase' = [phase EXCEPT ![m.dst] = "tree"]
  /\ treeParent' = [treeParent EXCEPT ![m.dst] = m.src]
  /\ UNCHANGED << treeReady, ackedReady >>

StartReady(n) ==
  /\ phase[n] = "tree"
  /\ phase' = [phase EXCEPT ![n] = "ready"]
  /\ UNCHANGED << treeParent, treeReady, ackedReady >>

DeliverReady(m) ==
  /\ m.kind = "ready"
  /\ phase' = [phase EXCEPT ![m.dst] = "done"]
  /\ treeReady' = [treeReady EXCEPT ![m.src] = TRUE]
  /\ ackedReady' = [ackedReady EXCEPT ![m.dst] = TRUE]
  /\ UNCHANGED << treeParent >>

\* Once the initiator has acked every ready child, the tree is quiescent.
Quiesce ==
  /\ phase[initiator] = "ready"
  /\ \A c \in R : ackedReady[c]
  /\ phase' = [phase EXCEPT ![initiator] = "done"]
  /\ UNCHANGED << treeParent, treeReady, ackedReady >>

Next ==
  \/ Quiesce
  \/ \E n \in Node : StartTree(n) \/ StartReady(n)
  \/ \E m \in Messages : DeliverTree(m) \/ DeliverReady(m)

\* The initiator is the unique root of the constructed spanning tree.
AncestorProperties ==
  /\ \A n \in Node : n # initiator => (treeParent[n] # NoNode)
  /\ \A n \in Node : (treeParent[n] # NoNode) => (Anc(treeParent[n]) = "root")
  /\ \A a, b \in Node : (treeParent[b] = a) => (Anc(b) = a)

\* Variant that serialises the network at startup and prints the graph shape.
TestSpec == Init /\ [][Next]_Vars

====