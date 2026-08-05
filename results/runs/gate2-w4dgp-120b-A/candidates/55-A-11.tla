---- MODULE MCEcho ----
EXTENDS Naturals

\* This configuration module instantiates the Echo spanning-tree algorithm
\* with a concrete, fully-connected three-node graph.  The underlying Echo
\* specification (re-exported below) defines the full set of actions and
\* properties; this file only sets the constants and extends the spec with
\* a test variant that prints the graph adjacency relation at runtime.
\* The .cfg substitutes concrete values for N1, I1, and R1.

CONSTANTS Node, initiator, R, NoNode

TypeOK ==
  /\ initiator \in Node
  /\ R \in [Node -> SUBSET Node]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ awake \in [Node -> BOOLEAN]
  /\ sent \in [Node -> BOOLEAN]

Init ==
  /\ initiator \in Node
  /\ parent = [n \in Node |-> NoNode]
  /\ awake = [n \in Node |-> n = initiator]
  /\ sent = [n \in Node |-> FALSE]

InitTest ==
  /\ Init
  /\ sent' = sent

\* Echo's actions (unmodified): the initiator awakens all nodes, a node
\* adopts a parent it can hear from, and a node wakes up via a heard
\* message.  The test variant prints the graph at runtime.
AwakenAll(n) ==
  /\ awake[n] = FALSE
  /\ awake' = [awake EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, sent>>

AdoptParent(n, p) ==
  /\ awake[n]
  /\ awake[p]
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = p]
  /\ UNCHANGED <<awake, sent>>

Broadcast(n) ==
  /\ awake[n]
  /\ sent[n] = FALSE
  /\ sent' = [sent EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, awake>>

WakeUp(n, p) ==
  /\ awake[n] = FALSE
  /\ sent[p]
  /\ awake[p]
  /\ awake' = [awake EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, sent>>

Next ==
  \/ \E n \in Node : AwakeAll(n)
  \/ \E n \in Node, p \in Node : AdoptParent(n, p)
  \/ \E n \in Node : Broadcast(n)
  \/ \E n \in Node, p \in Node : WakeUp(n, p)

Spec ==
  /\ \E n \in Node : Init /\ [][Next]_<<parent, awake, sent>>
  /\ \E n \in Node : Init /\ [][Next \cup {AwakenAll(n)}]_<<parent, awake, sent>>

AncestorProperties ==
  /\ \A n \in Node : initiator \in NodesReachable(n)
  /\ \A n \in Node : initiator \in NodesReaching(n)
  /\ \A n \in Node : NoNode \notin NodesReachable(n)

TestSpec == Spec

====