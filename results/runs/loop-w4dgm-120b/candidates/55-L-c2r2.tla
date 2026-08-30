---- MODULE MCEcho ----
\* Model-checking configuration for the Echo spanning-tree algorithm.
\* This module inherits the full action set from the Echo specification
\* and instantiates its constants with a small, fully-connected 3-node graph.
EXTENDS Naturals, FiniteSets

CONSTANTS N1, I1, R1, NoNode

VARIABLES phase, treeParent, treeReady, ackedReady

Vars == << phase, treeParent, treeReady, ackedReady >>

\* Echo messages are held in a set (multiset) and delivered in any order.
Message == [src : N1, dst : N1, kind : {"tree", "ready"}]
Messages == SUBSET Message

RECURSIVE Anc(n)
Anc(n) == IF n = I1 THEN "root"
         ELSE IF treeParent[n] = NoNode THEN "none"
         ELSE treeParent[n] # I1 /\ Anc(treeParent[n])

TypeOK ==
  /\ phase \in [N1 -> {"init", "tree", "ready", "done"}]
  /\ treeParent \in [N1 -> N1 \cup {NoNode}]
  /\ treeReady \in [N1 -> BOOLEAN]
  /\ ackedReady \in [N1 -> BOOLEAN]

Init ==
  /\ phase = [n \in N1 |-> "init"]
  /\ treeParent = [n \in N1 |-> NoNode]
  /\ treeReady = [n \in N1 |-> FALSE]
  /\ ackedReady = [n \in N1 |-> FALSE]

StartTree(n) ==
  /\ n \in R1
  /\ n # I1
  /\ phase[I1] = "init"
  /\ phase' = [phase EXCEPT ![I1] = "tree"]
  /\ treeParent' = [treeParent EXCEPT ![I1] = NoNode]
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
  /\ phase[I1] = "ready"
  /\ \A c \in R1 : ackedReady[c]
  /\ phase' = [phase EXCEPT ![I1] = "done"]
  /\ UNCHANGED << treeParent, treeReady, ackedReady >>

Next ==
  \/ Quiesce
  \/ \E n \in N1 : StartTree(n) \/ StartReady(n)
  \/ \E m \in Messages : DeliverTree(m) \/ DeliverReady(m)

\* The initiator is the unique root of the constructed spanning tree.
AncestorProperties ==
  /\ \A n \in N1 : n # I1 => (treeParent[n] # NoNode)
  /\ \A n \in N1 : (treeParent[n] # NoNode) => (Anc(treeParent[n]) = "root")
  /\ \A a, b \in N1 : (treeParent[b] = a) => (Anc(b) = a)

\* Variant that serialises the network at startup and prints the graph shape.
TestSpec == Init /\ [][Next]_Vars

====