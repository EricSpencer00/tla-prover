---- MODULE MCEcho ----
EXTENDS Naturals

(* Model-checking configuration module for the Echo spanning tree algorithm.  It   *)
(* instantiates the Echo specification with a concrete, fully-connected 3-node    *)
(* graph (every distinct pair of nodes is an edge), so a model checker can       *)
(* explore the full state space.  The module re-exports the Echo operators as     *)
(* top-level names, since the reference .cfg expects them there.                  *)

CONSTANTS Node, initiator, R, NoNode

N1 == N
I1 == I
R1 == R

VARIABLES parent, nextParent, visited, done

vars == <<parent, nextParent, visited, done>>

TypeOK ==
  /\ parent \in [N -> N \cup {NoNode}]
  /\ nextParent \in [N -> N \cup {NoNode}]
  /\ visited \subseteq N
  /\ done \subseteq N

Init ==
  /\ parent = [n \in N |-> NoNode]
  /\ nextParent = [n \in N |-> NoNode]
  /\ visited = {}
  /\ done = {}

Start(n) ==
  /\ parent[n] = NoNode
  /\ nextParent' = [nextParent EXCEPT ![n] = n]
  /\ UNCHANGED <<parent, visited, done>>

Send(m, n) ==
  /\ nextParent[m] = n
  /\ <<parent', nextParent', visited>> =
       [parent EXCEPT ![n] = m,
        nextParent EXCEPT ![m] = NoNode,
        visited' = visited \cup {n}]
  /\ UNCHANGED done

Ack(m) ==
  /\ parent[m] \in N
  /\ parent[m] \notin visited
  /\ nextParent[m] = NoNode
  /\ visited' = visited \cup {parent[m]}
  /\ UNCHANGED <<parent, nextParent, done>>

MarkDone(m) ==
  /\ parent[m] \in N
  /\ parent[m] \in visited
  /\ done' = done \cup {m}
  /\ UNCHANGED <<parent, nextParent, visited>>

Done == done = N

Next ==
  \/ \E n \in N : Start(n)
  \/ \E m, n \in N : Send(m, n)
  \/ \E m \in N : Ack(m)
  \/ \E m \in N : MarkDone(m)
  \/ (Done /\ UNCHANGED vars)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E m \in N : Ack(m))
  /\ WF_vars(\E m \in N : MarkDone(m))

AncestorProperties ==
  /\ initiator \in visited
  /\ \A m \in N : (m \in visited) => (initiator \in (m) ^+ parent)
  /\ \A a, b \in N : (a \in (b) ^+ parent) => (b \notin (a) ^+ parent)

TestSpec ==
  /\ Init
  /\ [][Next]_vars

====