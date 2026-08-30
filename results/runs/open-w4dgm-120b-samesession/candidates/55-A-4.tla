---- MODULE MCEcho ----
EXTENDS Integers

\* Echo spanning tree model checking configuration.
\* Overrides all parameter constants in Echo.tla with a concrete
\* three-node fully-connected graph (every distinct pair linked).
\* The sentinel value NoNode is declared as a model value.
CONSTANTS Node, initiator, R, NoNode

VARIABLES active, parent, target, epoch

vars == <<active, parent, target, epoch>>

ActiveEdges == {<<n, m>> : n \in active, m \in active}

\* Snapshots of the target[.] and parent[.] maps as plain sets of
\* pairs, for the two sub-properties in AncestorProperties.
Links == {<<n, m>> : \E c \in R : target[c] = <<n, m>>}
Parents == {<<n, m>> : m \in Node /\ parent[m] = n}

TypeOK ==
  /\ active \subseteq Node
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ target \in [R -> (Node \X Node) \cup {NoNode}]
  /\ epoch \in [Node -> 0..1]

Init ==
  /\ active = Node
  /\ parent = [n \in Node |-> IF n = initiator THEN n ELSE NoNode]
  /\ target = [c \in R |-> NoNode]
  /\ epoch = [n \in Node |-> 0]

\* An active node nominates a yet-unreached node as its spanning-tree
\* parent and arms an edge to it; both the parent map and the pledge
\* are written in the same atomic step.
Nominate(c) ==
  /\ target[c] = NoNode
  /\ LET n == c.from
         m == c.to IN
    /\ n \in active
    /\ m \in active
    /\ parent[m] = NoNode
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ target' = [target EXCEPT ![c] = <<n, m>>]
    /\ UNCHANGED <<active, epoch>>

\* The target node accepts, confirms the spanning-tree edge, and
\* clears the pledge on that edge.
Accept(c) ==
  /\ target[c] # NoNode
  /\ LET n == target[c][1]
         m == target[c][2] IN
    /\ <<n, m>> \in ActiveEdges
    /\ target' = [target EXCEPT ![c] = NoNode]
    /\ epoch' = [epoch EXCEPT ![m] = 1 - @]
    /\ UNCHANGED <<active, parent>>

\* A pledge that cannot be confirmed is dropped.
Drop(c) ==
  /\ target[c] # NoNode
  /\ LET n == target[c][1]
         m == target[c][2] IN
    /\ <<n, m>> \notin ActiveEdges
    /\ target' = [target EXCEPT ![c] = NoNode]
    /\ UNCHANGED <<active, parent, epoch>>

\* The initiator injects the first spanning-tree edge from a node that
\* has no parent yet.
Initiate ==
  /\ parent[initiator] = initiator
  /\ \E m \in active \ {initiator}:
       /\ parent[m] = NoNode
       /\ parent' = [parent EXCEPT ![m] = initiator]
       /\ target' = [t \in R |-> IF t = CHOOSE c \in R : c.from = initiator /\ c.to = m
                                 THEN <<initiator, m>> ELSE target[t]]
  /\ UNCHANGED <<active, epoch>>

\* A node is retired from the active set.
Retire(n) ==
  /\ n \in active
  /\ Cardinality(active) > 1
  /\ n # initiator
  /\ parent[n] = NoNode
  /\ active' = active \ {n}
  /\ UNCHANGED <<parent, target, epoch>>

\* A retired node is re-admitted.
Admit(n) ==
  /\ n \notin active
  /\ active' = active \cup {n}
  /\ UNCHANGED <<parent, target, epoch>>

Next ==
  \/ \E c \in R: Nominate(c) \/ Accept(c) \/ Drop(c)
  \/ Initiate
  \/ \E n \in Node: Retire(n) \/ Admit(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Initiate)

\* The initiator reaches every other node: no node is left parentless.
AncestorProperties ==
  /\ \A m \in Node: (m # initiator) => (parent[m] # NoNode)
  /\ \A x \in Node: (x # initiator) => (x \in {y \in Node: parent[y] = x} \cup
                                      {y \in Node: parent[parent[y]] = x})

\* Prints the adjacency relation to the console at the start of a run
\* (test output, not part of the algorithm).
TestSpec == Spec /\ (UNCHANGED vars) /\ (Print <<ActiveEdges>>) = 0

====