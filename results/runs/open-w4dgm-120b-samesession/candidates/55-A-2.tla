---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

\* The Echo spanning tree algorithm over a small fully-connected graph.
\* The initiator is chosen deterministically from the node set.  This module
\* adds no new state or actions to the underlying Echo spec; it only fixes
\* the constants for exhaustive model checking.

AllNodes == Node

VARIABLES parent, echoEnv, down, done

Vars == <<parent, echoEnv, down, done>>

TypeOK ==
  /\ parent \in [AllNodes -> AllNodes \cup {NoNode}]
  /\ echoEnv \in [AllNodes -> SUBSET AllNodes]
  /\ down \in [AllNodes -> SUBSET R]
  /\ done \subseteq AllNodes

Init ==
  /\ parent = [n \in AllNodes |-> NoNode]
  /\ echoEnv = [n \in AllNodes |-> {}]
  /\ down = [n \in AllNodes |-> {}]
  /\ done = {}

\* The initiator starts a flood fill: it marks itself done and records
\* every other node as a neighbor it has seen.
Start(n) ==
  /\ n = initiator
  /\ n \notin done
  /\ done' = {n}
  /\ down' = [down EXCEPT ![n] = (down[n] \cup (AllNodes \ {n}))]
  /\ UNCHANGED <<parent, echoEnv>>

\* A done node records a neighbor's resource as seen and passes the echo
\* back toward the initiator as it learns about new resources.
Seen(n, m) ==
  /\ n \in done
  /\ m \in down[n]
  /\ n \notin echoEnv[m]
  /\ echoEnv' = [echoEnv EXCEPT ![m] = @ \cup {n}]
  /\ UNCHANGED <<parent, down, done>>

\* Nodes adopt their parent when they first see an echo from it.  The
\* initiator never adopts anyone as parent.
Adopt(n, p) ==
  /\ parent[n] = NoNode
  /\ n # initiator
  /\ p \in echoEnv[n]
  /\ parent' = [parent EXCEPT ![n] = p]
  /\ done' = {n} \cup done
  /\ down' = [down EXCEPT ![p] = @ \cup {n}]
  /\ UNCHANGED echoEnv

\* A node that has adopted a parent and learned nothing new simply passes
\* its echo back toward the initiator and becomes quiescent.
Relay(n) ==
  /\ n \in done
  /\ n # initiator
  /\ parent[n] # NoNode
  /\ echoEnv[n] = {}
  /\ echoEnv' = [echoEnv EXCEPT ![parent[n]] = @ \cup {n}]
  /\ down' = [down EXCEPT ![parent[n]] = @ \cup {n}]
  /\ UNCHANGED <<parent, done>>

Next ==
  \/ \E n \in AllNodes : Start(n)
  \/ \E n \in AllNodes, m \in AllNodes : Seen(n, m)
  \/ \E n \in AllNodes, p \in AllNodes : Adopt(n, p)
  \/ \E n \in AllNodes : Relay(n)

\* The initiator is its own ancestor at the start; other nodes gain theirs
\* as they adopt parents while the tree is built.
Ancestor(x, y) ==
  IF x = y THEN TRUE
  ELSE IF parent[y] = NoNode THEN FALSE
  ELSE Ancestor(x, parent[y])

AncestorProperties ==
  /\ initiator \in done
  /\ \A n \in AllNodes \ {initiator} : parent[n] # NoNode
  /\ \A n \in AllNodes \ {initiator} : initiator \in AncestorSet(n)
  /\ \A n \in AllNodes \ {initiator} : ~Ancestor(n, initiator)
  /\ \A x, y \in AllNodes : (Ancestor(x, y) /\ Ancestor(y, x)) => x = y

AncestorSet(n) == {x \in AllNodes : Ancestor(x, n)}

TestSpec == Init /\ [][Next]_Vars

====