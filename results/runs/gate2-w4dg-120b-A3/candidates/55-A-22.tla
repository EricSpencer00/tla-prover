---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

RECURSIVE Intersects(_, _)
Intersects(S, T) ==
  \/ \E x \in S : x \in T
  \/ \E y \in S : \E z \in T : Intersects({y}, {z})

VARIABLES parent, done, presence

vars == <<parent, done, presence>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ done \in [Node -> BOOLEAN]
  /\ presence \subseteq [a: Node, b: Node]

AncestorProperties ==
  /\ \A n \in Node : done[n] => parent[n] # NoNode => (parent[n] \in Node /\ parent[n] # n)
  /\ \A x \in Node : (\A y \in Node : (done[x] /\ done[y] /\ x # y) => ((x, y) \in presence \/ (y, x) \in presence))
  /\ \A x \in Node : (x \in {n \in Node : parent[n] # NoNode} => parent[x] \in {n \in Node : parent[n] # NoNode})

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE initiator]
  /\ done = [n \in Node |-> FALSE]
  /\ presence = {}

TreeStep ==
  /\ \E n \in Node, m \in Node :
       /\ ~done[m]
       /\ parent[n] = m
       /\ done' = [done EXCEPT ![m] = TRUE]
  /\ UNCHANGED <<parent, presence>>

Rewire ==
  /\ \E n \in Node, m \in Node :
       /\ ~done[n]
       /\ n \in {w \in Node : parent[w] # NoNode}
       /\ presence' = presence \cup {[a |-> n, b |-> m]}
       /\ parent' = [parent EXCEPT ![n] = m]
  /\ UNCHANGED done

Next ==
  \/ TreeStep
  \/ Rewire

TestSpec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(TreeStep)

Spec == TestSpec

====