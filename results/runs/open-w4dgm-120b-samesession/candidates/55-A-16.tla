---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

\* Model-checking configuration for the Echo spanning tree algorithm. This
\* module provides *no* new behavior compared to the Echo specification; it
\* simply fixes the constants so that a small, fully-connected three-node
\* graph is explored exhaustively by TLC. The test variant emits the graph
\* (as a debugging aid) and then behaves exactly like the original spec.
CONSTANTS Node, initiator, R, NoNode

ASSUME /\ NoNode \notin Node
       /\ initiator \in Node

\* MaxState bounds the window of concurrent Echo rounds that may be in
\* flight; the number of distinct round labels the model actually uses.
MaxState == 2

VARIABLES parent, pending, echoState, roundOf, roundCount

vars == <<parent, pending, echoState, roundOf, roundCount>>

\* The graph is an adjacency relation: a set of undirected edges. The
\* configuration below makes it the complete graph on the three nodes.
Edges == {{n1, n2} : n1 \in Node, n2 \in Node, n1 # n2}

Neighbors(n) == {m \in Node : {n, m} \in Edges}

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ pending \subseteq Node
  /\ echoState \in {"idle", "inFlight"}
  /\ roundOf \in [Node -> 0..MaxState]
  /\ roundCount \in 0..MaxState

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ pending = {}
  /\ echoState = "idle"
  /\ roundOf = [n \in Node |-> 0]
  /\ roundCount = 0

\* The initiator starts an Echo round that floods the whole mesh.
StartEcho ==
  /\ echoState = "idle"
  /\ roundCount < MaxState
  /\ echoState' = "inFlight"
  /\ roundCount' = roundCount + 1
  /\ roundOf' = [n \in Node |-> roundCount + 1]
  /\ parent' = [n \in Node |-> IF n = initiator THEN initiator ELSE NoNode]
  /\ pending' = {n \in Node : n # initiator}

\* Echo messages arrive in any order; each node hops on its first one.
ProcessEcho(n) ==
  /\ echoState = "inFlight"
  /\ n \in pending
  /\ parent[n] = NoNode
  /\ \E a \in Neighbors(n) : parent[a] = roundOf[n]
  /\ parent' = [parent EXCEPT ![n] = roundOf[n]]
  /\ pending' = pending \ {n}
  /\ UNCHANGED <<echoState, roundOf, roundCount>>

\* When every node has been placed the round closes on its own.
CloseRound ==
  /\ echoState = "inFlight"
  /\ pending = {}
  /\ echoState' = "idle"
  /\ UNCHANGED <<parent, pending, roundOf, roundCount>>

\* The test variant: it prints the graph adjacency once, then does nothing
\* further and lets the original Echo actions take over.
TestEcho ==
  /\ roundCount = 0
  /\ (Edges = {}
        \/ \A n1, n2 \in Node : n1 # n2 => {n1, n2} \in Edges)
  /\ UNCHANGED vars

Next ==
  \/ StartEcho
  \/ \E n \in Node : ProcessEcho(n)
  \/ CloseRound
  \/ TestEcho

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node : (n # initiator) => (parent[n] # NoNode)
  /\ ~\E n \in Node : (parent[n] # NoNode) /\ (parent[parent[n]] # NoNode)
  /\ \A n \in Node : (parent[n] # NoNode) ~> (parent[n] = initiator)

TestSpec == Spec /\ AncestorProperties

\* .cfg replaces Name with a bounded instantiation of Name (a finite set
\* or a restricted integer range) before TLC runs, so N1/I1/R1 below are
\* *not* literals but placeholders for that substitution.
N1 == Node
I1 == initiator
R1 == R
====