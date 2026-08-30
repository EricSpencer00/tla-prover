---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

\* The Echo algorithm runs on a connected undirected graph and converges to a
\* spanning tree. This module instantiates it with a concrete three-node mesh.

VARIABLES parent, active, origin, done

vars == <<parent, active, origin, done>>

RECURSIVE Ancestors(_)
Ancestors(n) ==
  IF parent[n] = NoNode THEN {}
  ELSE {parent[n]} \cup Ancestors(parent[n])

Init ==
  /\ parent  = [n \in Node |-> NoNode]
  /\ active  = Node
  /\ origin  = initiator
  /\ done    = {}

\* The initiator begins the echo down the tree it is (the config's) responsibility.
EchoStarter ==
  /\ origin \in active
  /\ parent[origin] = NoNode
  /\ (\A m \in Node : parent[m] # origin)
  /\ active' = active \ {origin}
  /\ parent' = [parent EXCEPT ![origin] = origin]
  /\ UNCHANGED <<origin, done>>

\* A node echoes to a neighbor that has no parent yet.
Echo(n, m) ==
  /\ n \in active
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ active' = active \ {n} \cup {m}
  /\ UNCHANGED <<origin, done>>

\* A node with a parent and no active children finishes and shuts down.
Close(n) ==
  /\ n \notin active
  /\ \A m \in Node : parent[m] # n
  /\ n \notin done
  /\ done' = done \cup {n}
  /\ UNCHANGED <<parent, active, origin>>

\* Once every node has recorded its parent, the initiator closes and the tree is
\* quiescent.
InitiatorClose ==
  /\ origin \notin active
  /\ \A m \in Node : parent[m] # NoNode
  /\ origin \notin done
  /\ done' = done \cup {origin}
  /\ UNCHANGED <<parent, active, origin>>

Next ==
  \/ EchoStarter
  \/ \E n, m \in Node : Echo(n, m)
  \/ \E n \in Node : Close(n)
  \/ InitiatorClose

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(EchoStarter)
  /\ \A n \in Node : SF_vars(Close(n))
  /\ WF_vars(InitiatorClose)

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ active \subseteq Node
  /\ origin \in Node
  /\ done \subseteq Node

AncestorProperties ==
  /\ (\A m \in Node : m # initiator => parent[m] # NoNode)
  /\ (initiator \notin done => origin = initiator)
  /\ \A n \in Node : n \in done => initiator \in Ancestors(n)
  /\ \A n \in Node : n \in done => n \notin Ancestors(n)

PrintGraph ==
  /\ \E e \in Node \X Node :
       /\ e[1] # e[2]
       /\ Cardinality({x \in {e[1], e[2]} : TRUE}) = 2
       /\ ~(\A o \in Node : \A d \in Node :
              <<o, d>> \in R => Cardinality({o, d}) = 2)
  /\ UNCHANGED vars

TestSpec ==
  /\ Spec
  /\ PrintGraph

====