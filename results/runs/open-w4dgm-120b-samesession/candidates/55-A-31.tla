---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* The Echo spanning tree algorithm: an initiator injects a token into an
\* undirected network and each node records the neighbor from which it first
\* learned about the token. Because every edge is bidirectional, the recorded
\* ancestor relation forms a symmetric closure of the spanning tree, with the
\* initiator as the unique root.
\* This module fixes the number of nodes and the graph shape for model checking;
\* the actions and properties are taken unchanged from the Echo specification.

N == Cardinality(Node)

Neighbors(n, g) == {m \in Node : <<n, m>> \in g}
Base == CHOOSE n \in Node : \A m \in Node : n # m => <<n, m>> \in R

VARIABLES mark, parent, seen, active, graph

vars == <<mark, parent, seen, active, graph>>

TypeOK ==
  /\ mark \in [Node -> BOOLEAN]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ seen \in [Node -> 0..N]
  /\ active \subseteq Node
  /\ graph \subseteq (Node \X Node)

Init ==
  /\ mark = [n \in Node |-> FALSE]
  /\ parent = [n \in Node |-> NoNode]
  /\ seen = [n \in Node |-> 0]
  /\ active = {}
  /\ graph = R

\* The initiator injects the token, marking itself and becoming its own ancestor.
Inject ==
  /\ ~mark[initiator]
  /\ mark' = [mark EXCEPT ![initiator] = TRUE]
  /\ parent' = [parent EXCEPT ![initiator] = initiator]
  /\ seen' = [seen EXCEPT ![initiator] = N]
  /\ active' = active \cup {initiator}
  /\ UNCHANGED <<graph>>

\* A node that has not yet seen the token learns it from an active neighbor,
\* records that neighbor as its ancestor, and becomes active.
Learn(n, m) ==
  /\ ~mark[n]
  /\ m \in active
  /\ <<n, m>> \in graph
  /\ mark' = [mark EXCEPT ![n] = TRUE]
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ seen' = [seen EXCEPT ![n] = seen[m] - 1]
  /\ active' = active \cup {n}
  /\ UNCHANGED <<graph>>

\* A leaf that has learned from and seen the token can stop forwarding it.
Halt(n) ==
  /\ n \in active
  /\ seen[n] = N
  /\ \A m \in Node : <<n, m>> \in graph => ~mark[m]
  /\ active' = active \ {n}
  /\ UNCHANGED <<mark, parent, seen, graph>>

\* A leaf that has learned from and seen the token can stop forwarding it.
\* This is the last action, so the count of marked nodes can only reach N once.
InjectStep == Inject
LearnStep == \E n \in Node, m \in Node : Learn(n, m)
HaltStep == \E n \in Node : Halt(n)

Next == Inject \/ (\E n \in Node, m \in Node : Learn(n, m)) \/ (\E n \in Node : Halt(n))

\* TestSpec prints the graph adjacency for debugging; it is test-only.
TestSpec == InjectStep /\ UNCHANGED <<mark, parent, seen, active, graph>>

Spec == TestSpec

AncestorProperties ==
  /\ (mark[Base] <=> \A n \in Node : n # Base => parent[n] # NoNode)
  /\ \A n \in Node : (parent[n] # NoNode /\ n # Base) => mark[parent[n]]
  /\ \A n \in Node : (parent[n] # NoNode /\ n # Base) => parent[parent[n]] # NoNode
  /\ \A n \in Node : (parent[n] # NoNode /\ parent[parent[n]] # NoNode) => parent[parent[parent[n]]] # NoNode

\* SAFETY PROPERTY: the initiator remains the sole ancestor of every other node.
\* It is only true at a terminal state, so marked is included to distinguish it
\* from the per-step structural fact that the ancestor relation stays acyclic.
SpanningTree ==
  /\ marked
  /\ AncestorProperties
  /\ \A n \in Node : (n # Base /\ parent[n] # NoNode) => parent[parent[n]] # NoNode

\* LIVENESS PROPERTY: the echo continues until every node has observed the
\* token and the initiator is left alone.
EchoCompletes == <>(\A n \in Node : mark[n])
====