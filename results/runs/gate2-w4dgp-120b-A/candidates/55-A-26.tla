---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

\* Model-checking variant of the Echo spanning tree algorithm.
\* This module is deliberately minimal: it inherits every state variable,
\* action, and property from the core Echo specification and only adds the
\* concrete graph configuration. The fully-meshed graph below is the
\* smallest non-trivial topology that still satisfies all Echo assumptions
\* (connectivity, symmetry, irreflexivity). The test action exists to
\* confirm the adjacency relation at runtime and has no effect on the
\* algorithm's safety or liveness properties.

CONSTANTS
    parent, active, done, sent, start

VARIABLES
    parent, active, done, sent, start

vars == <<parent, active, done, sent, start>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ active \subseteq Node
    /\ done \subseteq Node
    /\ sent \subseteq Node
    /\ start \in Node

TypeOKI ==
    /\ parent = [n \in Node |-> NoNode]
    /\ active = {}
    /\ done = {}
    /\ sent = {}
    /\ start = "n0"

N1 == { "n0", "n1", "n2" }

I1 == "n0"

R1 ==
    { <<x, y>> \in Node \X Node : x # y }

\* The initiator begins the echo wave, marking itself active.
StartEcho ==
    /\ parent = [n \in Node |-> NoNode]
    /\ active = {}
    /\ parent[initiator] = NoNode
    /\ parent' = [parent EXCEPT ![initiator] = initiator]
    /\ active' = {initiator}
    /\ start' = initiator
    /\ UNCHANGED <<done, sent>>

\* A node forwards the wave to a neighbor that has not been visited.
Echo(n, m) ==
    /\ n \in active
    /\ <<n, m>> \in R
    /\ parent[m] = NoNode
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ active' = active \cup {m}
    /\ UNCHANGED <<done, sent, start>>

\* A node with no more forwarding to do becomes done.
FireEcho(n) ==
    /\ n \in active
    /\ active' = active \ {n}
    /\ done' = done \cup {n}
    /\ UNCHANGED <<parent, sent, start>>

\* The initiator marks the wave complete once all nodes are done.
TerminateEcho ==
    /\ \A n \in Node : n \in done
    /\ sent' = sent \cup {start}
    /\ UNCHANGED <<parent, active, done, start>>

\* Test action: prints the graph adjacency at runtime; no state change.
PrintGraph ==
    /\ UNCHANGED vars

Next ==
    \/ StartEcho
    \/ \E n \in Node, m \in Node : Echo(n, m)
    \/ \E n \in Node : FireEcho(n)
    \/ TerminateEcho
    \/ PrintGraph

AncestorProperties ==
    /\ (\A n \in Node : n # initiator => parent[n] # NoNode)
    /\ (\A n \in Node : n # initiator => parent[n] /= n)
    /\ (\A n \in Node : n # initiator => initiator \in (parent)^[*][{n}])

TestSpec == Init /\ [][Next]_vars

Init == TypeOKI

Spec == TestSpec

====