---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sent, echoed, echoCount, root

vars == <<parent, sent, echoed, echoCount, root>>

Nodes == Node
Edges == {p \in Nodes \X Nodes : p[1] # p[2]}
InitS == CHOOSE s \in initiator : TRUE

TypeOK ==
  /\ parent \in [Nodes -> Nodes \cup {NoNode}]
  /\ sent \subseteq Edges
  /\ echoed \subseteq Nodes
  /\ echoCount \in [Nodes -> 0..Cardinality(R)]
  /\ root \in Nodes

AncestorProperties ==
  /\ \A n \in Nodes : (n # root) => (parent[n] # NoNode)
  /\ \A n \in Nodes : (n # root /\ parent[n] # NoNode) => (parent[parent[n]] # NoNode)

Init ==
  /\ parent = [n \in Nodes |-> NoNode]
  /\ sent = {}
  /\ echoed = {}
  /\ echoCount = [n \in Nodes |-> 0]
  /\ root = InitS

Emit(n, m) ==
  /\ <<n, m>> \notin sent
  /\ sent' = sent \cup {<<n, m>>}
  /\ UNCHANGED <<parent, echoed, echoCount, root>>

Adopt(n, m) ==
  /\ parent[n] = NoNode
  /\ n # m
  /\ <<m, n>> \in sent
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ UNCHANGED <<sent, echoed, echoCount, root>>

Echo(n) ==
  /\ parent[n] # NoNode
  /\ n \notin echoed
  /\ echoed' = echoed \cup {n}
  /\ echoCount' = [echoCount EXCEPT ![parent[n]] = @ + 1]
  /\ UNCHANGED <<parent, sent, root>>

Quiesce ==
  /\ (root # NoNode => root \in echoed)
  /\ echoed = Nodes
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes, m \in Nodes : Emit(n, m)
  \/ \E n \in Nodes, m \in Nodes : Adopt(n, m)
  \/ \E n \in Nodes : Echo(n)
  \/ Quiesce

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Quiesce)

TestSpec ==
  /\ Spec
  /\ UNCHANGED vars

N1 == Nodes
I1 == initiator
R1 == R
====