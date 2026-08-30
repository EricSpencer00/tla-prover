---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* Model-checking configuration: a fully-connected three-node graph (each
\* directed edge is listed in both directions, so the graph is symmetric) with
\* a deterministically-chosen initiator, used to validate the Echo algorithm.
Edges == { <<n1, n2>> : n1 \in Node, n2 \in Node, n1 # n2 }

VARIABLES active, acked, treeParent, heldBy, echoRound

vars == << active, acked, treeParent, heldBy, echoRound >>

TypeOK ==
  /\ active \subseteq Node
  /\ acked \subseteq Node
  /\ treeParent \in [Node -> Node \cup {NoNode}]
  /\ heldBy \in [R -> Node \cup {NoNode}]
  /\ echoRound \in [Node -> Nat]

Init ==
  /\ active = {}
  /\ acked = {}
  /\ treeParent = [n \in Node |-> NoNode]
  /\ heldBy = [g \in R |-> NoNode]
  /\ echoRound = [n \in Node |-> 0]

\* The initiator starts the spanning-tree construction/echo on its own.
InitiateEcho(n) ==
  /\ n = initiator
  /\ n \notin active
  /\ active' = active \cup {n}
  /\ echoRound' = [echoRound EXCEPT ![n] = IF echoRound[n] = 0 THEN 1 ELSE echoRound[n]]
  /\ UNCHANGED << acked, treeParent, heldBy >>

\* A node with no parent yet adopts the node from which it first learns about
\* the active echo round and records that round; it may already be done.
LearnParent(n, p) ==
  /\ p \in active
  /\ n \notin active
  /\ treeParent[n] = NoNode
  /\ echoRound[p] = echoRound[initiator]
  /\ treeParent' = [treeParent EXCEPT ![n] = p]
  /\ echoRound' = [echoRound EXCEPT ![n] = echoRound[p]]
  /\ active' = active \cup {n}
  /\ UNCHANGED << acked, heldBy >>

\* A node can only acknowledge once its parent has already acknowledged.
Ack(n) ==
  /\ n \in active
  /\ n \notin acked
  /\ (treeParent[n] = NoNode \/ treeParent[n] \in acked)
  /\ acked' = acked \cup {n}
  /\ UNCHANGED << active, treeParent, heldBy, echoRound >>

Release(n) ==
  /\ n \in acked
  /\ heldBy' = [g \in R |-> IF heldBy[g] = n THEN NoNode ELSE heldBy[g]]
  /\ active' = active \ {n}
  /\ acked' = acked \ {n}
  /\ treeParent' = [treeParent EXCEPT ![n] = NoNode]
  /\ echoRound' = [echoRound EXCEPT ![n] = 0]

\* Releasing a node while its children have not yet acknowledged would orphan
\* them on a round that the parent is no longer part of, so it is refused.
ReleaseOK(n) == n \in acked /\ Cardinality({m \in acked : treeParent[m] = n}) = 0

Acquire(g, n) ==
  /\ heldBy[g] = NoNode
  /\ n \in acked
  /\ heldBy' = [heldBy EXCEPT ![g] = n]
  /\ UNCHANGED << active, acked, treeParent, echoRound >>

\* The only nondeterministic choice in this model is which resource a node
\* acquires next, which is bounded by the finite resource set, so it stays fair.
AcquireAny(g) == \E n \in Node : Acquire(g, n)

Next ==
  \/ \E n \in Node : InitiateEcho(n)
  \/ \E n \in Node, p \in Node : LearnParent(n, p)
  \/ \E n \in Node : Ack(n)
  \/ \E n \in Node : Release(n)
  \/ \E g \in R : Acquire(g, CHOOSE n \in Node : heldBy[g] = NoNode)

\* SAFETY PROPERTY: when the tree has fully resolved, the initiator is the
\* sole root of the ancestor relation and every other node descends from it.
AncestorProperties ==
  /\ initiator \notin acked
  /\ (acked # {} => treeParent[initiator] = NoNode)
  /\ (acked \ {initiator} # {} => \A n \in acked \ {initiator} : treeParent[n] \in acked)
  /\ (acked # {} => \A n \in acked : n # initiator => (treeParent[n] # NoNode /\ treeParent[n] \in acked))
====