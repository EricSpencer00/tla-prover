---- MODULE MCEcho ----
EXTENDS Integers

\* Model-checking configuration module for the Echo spanning tree algorithm.
\* This module instantiates the Echo specification with a concrete three-node
\* fully-connected graph, which bounds the state space so TLC can explore it
\* exhaustively. It also provides a test variant that prints the graph at
\* startup.

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sent, recv, phase

vars == << parent, sent, recv, phase >>

RECURSIVE ancestorsOf(_)
ancestorsOf(n) ==
    IF n = NoNode THEN {}
    ELSE {n} \cup ancestorsOf(parent[n])

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent = [n \in Node |-> 0]
    /\ recv = [n \in Node |-> 0]
    /\ phase = "idle"

SendEcho(n, m) ==
    /\ n = initiator \/ parent[n] # NoNode
    /\ sent[n] < 2
    /\ <<n, m>> \in R
    /\ parent[m] = NoNode
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ sent' = [sent EXCEPT ![n] = sent[n] + 1]
    /\ phase' = IF phase = "idle" /\ n = initiator THEN "searching" ELSE phase
    /\ UNCHANGED recv

ReceiveEcho(m) ==
    /\ parent[m] # NoNode
    /\ recv' = [recv EXCEPT ![m] = recv[m] + 1]
    /\ UNCHANGED << parent, sent, phase >>

FinishSearch ==
    /\ phase = "searching"
    /\ \A n \in Node : n # initiator => recv[n] >= 1
    /\ phase' = "done"
    /\ UNCHANGED << parent, sent, recv >>

Quit ==
    /\ phase = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node, m \in Node : SendEcho(n, m)
    \/ \E m \in Node : ReceiveEcho(m)
    \/ FinishSearch
    \/ Quit

Test ==
    BEGIN
        WRITE("\nGraph adjacency (each line is an undirected edge, one per line):\n")
        \E e \in R : BEGIN
            WRITE("\t", e[1], " <-> ", e[2], "\n")
        END
    END

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Test)

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ sent \in [Node -> 0..2]
    /\ recv \in [Node -> 0..2]
    /\ phase \in {"idle", "searching", "done"}

AncestorProperties ==
    /\ \A n \in Node : n # initiator => initiator \in ancestorsOf(n)
    /\ \A a, b \in Node : (a \in ancestorsOf(b) /\ a # b) => b \notin ancestorsOf(a)

====