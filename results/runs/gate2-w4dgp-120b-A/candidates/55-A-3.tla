---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, pending, inTree, bounced

vars == << parent, pending, inTree, bounced >>
N == Cardinality(Node)

TypeOK ==
  /\ parent \in [ Node -> Node \cup {NoNode} ]
  /\ pending \subseteq R
  /\ inTree \subseteq Node
  /\ bounced \subseteq Node

Init ==
  /\ parent = [ n \in Node |-> NoNode ]
  /\ pending = { [ from |-> n, to |-> n ] : n \in Node }
  /\ inTree = {}
  /\ bounced = {}

EchoStep ==
  \E m \in pending :
    /\ m.from \in inTree
    /\ m.to \notin inTree
    /\ parent' = [ parent EXCEPT ![m.to] = m.from ]
    /\ pending' = pending \ {m}
    /\ inTree' = inTree \cup {m.to}
    /\ UNCHANGED bounced

Bounce ==
  \E m \in pending :
    /\ m.to \in bounced
    /\ parent' = [ parent EXCEPT ![m.to] = NoNode ]
    /\ inTree' = inTree \ {m.to}
    /\ pending' = pending \cup { [ from |-> m.to, to |-> m.from ] }
    /\ UNCHANGED bounced

Drop ==
  \E m \in pending :
    /\ m.from \notin inTree
    /\ m.to \notin inTree
    /\ pending' = pending \ {m}
    /\ UNCHANGED << parent, inTree, bounced >>

Next == EchoStep \/ Bounce \/ Drop

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ (initiator \in inTree)
  /\ \A n \in Node \ {initiator} : n \in inTree
  /\ \A n \in Node : parent[n] # NoNode => parent[n] \in inTree
  /\ \A n \in Node : parent[n] = NoNode => n = initiator

TestSpec ==
  /\ Spec
  /\ UNCHANGED << Node, initiator, R, NoNode >>
  /\ (IF Cardinality(Node) = 0 THEN TRUE
        ELSE Print("Adjacency:", [ x \in Node, y \in Node |-> [x, y] \in R ]))
====