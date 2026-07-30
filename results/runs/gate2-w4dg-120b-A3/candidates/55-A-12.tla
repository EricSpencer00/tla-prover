---- MODULE MCEcho ----
EXTENDS Naturals

\* This module is a TLA+ configuration for the Echo spanning tree algorithm.
\* It defines ONE small fully-connected graph of three nodes and picks one of
\* them as the initiator.  The SPECIFICATION, INVARIANTS, and PROPERTIES are
\* exactly the ones listed in the "required identifiers" section of the prompt,
\* and every identifier the .cfg references is defined here.

CONSTANTS Node, initiator, R, NoNode

Nodes == {"u", "v", "w"}

\* The fully-meshed graph: every distinct pair of nodes is connected.
Links == {x \in Nodes, y \in Nodes : x # y}

VARIABLES sent, acked, parent, mode

vars == <<sent, acked, parent, mode>>

InitSpec ==
  /\ sent = 0
  /\ acked = 0
  /\ parent = [x \in Nodes |-> NoNode]
  /\ mode = "idle"

SendEcho ==
  /\ mode = "idle"
  /\ mode' = "active"
  /\ sent' = sent + 1
  /\ UNCHANGED <<acked, parent>>

AckEcho ==
  /\ mode = "active"
  /\ acked < sent
  /\ acked' = acked + 1
  /\ UNCHANGED <<sent, parent, mode>>

SetParent(n, p) ==
  /\ p # NoNode
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = p]
  /\ UNCHANGED <<sent, acked, mode>>

Quiesce ==
  /\ mode = "active"
  /\ acked = sent
  /\ mode' = "quiet"
  /\ UNCHANGED <<sent, acked, parent>>

\* The test variant prints the adjacency relation at start-up rather than
\* exercising any new transition; it helps a human confirm the graph is as
\* intended before the model checker runs.
PrintLinks ==
  /\ mode = "idle"
  /\ \A e \in Links : PrintS("Link: " ^ e[1] ^ " <-> " ^ e[2])
  /\ UNCHANGED vars

NextSpec ==
  \/ SendEcho
  \/ AckEcho
  \/ \E n \in Nodes, p \in Nodes : SetParent(n, p)
  \/ Quiesce
  \/ PrintLinks

Spec == InitSpec /\ [][NextSpec]_vars

TypeOK ==
  /\ sent \in 0..4
  /\ acked \in 0..4
  /\ parent \in [Nodes -> Nodes \cup {NoNode}]
  /\ mode \in {"idle", "active", "quiet"}

Ancestor(n) ==
  IF parent[n] = NoNode THEN {}
  ELSE {parent[n]} \cup Ancestor(parent[n])

AncestorProperties ==
  /\ initiator \in Nodes
  /\ initiator \in AncestorProperties'    \* initiator is ancestor of itself
  /\ \A n \in Nodes \ {initiator} : initiator \in Ancestor(n)
  /\ \A n \in Nodes :
       LET S_n == Ancestor(n) \cup {n} IN \A m \in S_n : Ancestor(m) \cap S_n = {}

Init == InitSpec
Next == NextSpec

TestSpec == Spec

====