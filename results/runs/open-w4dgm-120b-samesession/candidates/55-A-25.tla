---- MODULE MCEcho ----
EXTENDS Naturals

\* Model-checking configuration for the Echo spanning tree algorithm.
\* Builds a concrete three-node fully-connected graph (every distinct pair
\* of nodes is a link) and reuses the full Echo-spec action set on it.

CONSTANTS Node, initiator, R, NoNode

\* Every pair of distinct nodes is connected: the graph is fully meshed.
Neighbors(n) == {m \in Node : n # m}

VARIABLES inCS, parent, children, acked, announced, down

vars == <<inCS, parent, children, acked, announced, down>>

TypeOK ==
  /\ inCS \subseteq Node
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ acked \subseteq Node
  /\ announced \subseteq Node
  /\ down \subseteq Node

Init ==
  /\ inCS = {}
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ acked = {}
  /\ announced = {}
  /\ down = {}

\* The initiator begins the spanning tree.
Start(n) ==
  /\ inCS = {}
  /\ n = initiator
  /\ n \notin down
  /\ inCS' = {n}
  /\ parent' = [parent EXCEPT ![n] = n]
  /\ children' = [children EXCEPT ![n] = {}]
  /\ UNCHANGED <<acked, announced, down>>

\* A non-initiator joins by hearing from an already-in-tree neighbor.
Announce(n, p) ==
  /\ n \notin inCS
  /\ p \in inCS
  /\ p \in Neighbors(n)
  /\ n \notin down
  /\ inCS' = inCS \cup {n}
  /\ parent' = [parent EXCEPT ![n] = p]
  /\ children' = [children EXCEPT ![p] = children[p] \cup {n}]
  /\ UNCHANGED <<acked, announced, down>>

\* A node acknowledges to its parent once it is in the tree.
Ack(n) ==
  /\ n \in inCS
  /\ n \notin acked
  /\ n \notin down
  /\ acked' = acked \cup {n}
  /\ UNCHANGED <<inCS, parent, children, announced, down>>

\* Crash: a not-yet-acknowledged node goes down silently.
Crash(n) ==
  /\ n \in inCS
  /\ n \notin acked
  /\ n \notin down
  /\ down' = down \cup {n}
  /\ UNCHANGED <<inCS, parent, children, acked, announced>>

\* Recovery: a crashed node in the tree rejoins.
Recover(n) ==
  /\ n \in down
  /\ down' = down \ {n}
  /\ UNCHANGED <<inCS, parent, children, acked, announced>>

\* An operational in-tree node broadcasts once.
AnnounceOnce(n) ==
  /\ n \in inCS
  /\ n \notin down
  /\ n \notin announced
  /\ inCS = Node
  /\ announced' = announced \cup {n}
  /\ UNCHANGED <<inCS, parent, children, acked, down>>

Next ==
  \/ \E n \in Node : Start(n) \/ Ack(n) \/ Crash(n) \/ Recover(n) \/ AnnounceOnce(n)
  \/ \E n \in Node, p \in Node : Announce(n, p)

TestSpec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A n \in Node : SF_vars(Ack(n)))
  /\ (\A n \in Node : SF_vars(AnnounceOnce(n)))

\* The initiator is ancestor of all other nodes and the ancestor relation
\* is acyclic -- together these imply the spanning tree is a rooted tree.
AncestorProperties ==
  /\ \A n \in Node : n # initiator => (initiator \in descendants(n, parent))
  /\ \A n \in Node : n \notin descendants(n, parent)

descendants(n, par) ==
  LET rec(m) == IF m = NoNode THEN {}
                ELSE {m} \cup rec(par[m])
  IN rec(parent[n])

====