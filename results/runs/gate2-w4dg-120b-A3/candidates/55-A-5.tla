---- MODULE MCEcho ----
EXTENDS Naturals

\* Natural-language description: a model-checking configuration module for the Echo
\* spanning tree algorithm, instantiating a concrete three-node fully-connected
\* graph. All state and behavior are inherited from the Echo specification; this
\* module supplies only the concrete constants and the test variant that prints
\* the graph at startup. The .cfg drives which operator names are substituted for
\* the constants (Node, initiator, R) via the N1, I1, R1 operators defined below.
\* The NoNode constant is a model value distinct from any real node, used as the
\* sentinel for the "no parent" entry.

CONSTANTS Node, initiator, R, NoNode

GRAPH == [x \in Node |-> {y \in Node : y # x}]

VARIABLES parent, phase

vars == <<parent, phase>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ phase \in [Node -> {"idle", "active", "done"}]

AncestorProperties ==
    /\ \A n \in Node : initiator \in {n} \cup {parent[n]}
    /\ NoNode \notin {parent[n] : n \in Node}

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ phase = [n \in Node |-> "idle"]

Next == EchoNext

Spec == Init /\ [][Next]_vars

TestSpec == Init /\ [][Next]_vars
    /\ Cardinality(Node) = 3
    /\ Cardinality(initiator) = 1
    /\ \A a, b \in initiator : a = b
    /\ \A x, y \in Node : x \in GRAPH[y] <=> y \in GRAPH[x]
    /\ \A x \in Node : x \notin GRAPH[x]
    /\ \A n \in Node : parent[n] \in Node \cup {NoNode}
    /\ \A n \in Node : phase[n] \in {"idle", "active", "done"}
    /\ Print("\* TestSpec: Graph =", GRAPH)
    /\ TRUE

N1 == Node
I1 == initiator
R1 == GRAPH

====