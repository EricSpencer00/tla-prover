---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

Nodes == {"n1", "n2", "n3"}
Parents == Nodes \cup {NoNode}

VARIABLES parent, reached, waiting, echoing, done

vars == <<parent, reached, waiting, echoing, done>>

TypeOK ==
    /\ parent \in [Nodes -> Parents]
    /\ reached \subseteq Nodes
    /\ waiting \subseteq Nodes
    /\ echoing \subseteq Nodes
    /\ done \subseteq Nodes

InitState ==
    /\ parent = [n \in Nodes |-> NoNode]
    /\ reached = {}
    /\ waiting = {}
    /\ echoing = {}
    /\ done = {}

InitTree ==
    /\ parent' = [n \in Nodes |-> NoNode]
    /\ reached' = {initiator}
    /\ waiting' = {}
    /\ echoing' = {}
    /\ done' = {}

BeginWait(n) ==
    /\ n \in reached
    /\ n \notin waiting
    /\ n \notin echoing
    /\ n \notin done
    /\ waiting' = waiting \cup {n}
    /\ UNCHANGED <<parent, reached, echoing, done>>

SendEcho(n, m) ==
    /\ n \in waiting
    /\ n # m
    /\ waiting' = waiting \ {n}
    /\ echoing' = echoing \cup {m}
    /\ UNCHANGED <<parent, reached, done>>

AcceptEcho(m) ==
    /\ m \in echoing
    /\ m \notin reached
    /\ parent' = [parent EXCEPT ![m] = CHOOSE n \in waiting : TRUE]
    /\ reached' = reached \cup {m}
    /\ echoing' = echoing \ {m}
    /\ UNCHANGED <<waiting, done>>

MarkDone(n) ==
    /\ n \in reached
    /\ n \notin waiting
    /\ n \notin echoing
    /\ n \notin done
    /\ done' = done \cup {n}
    /\ UNCHANGED <<parent, reached, waiting, echoing>>

Halt ==
    /\ done = Nodes
    /\ UNCHANGED vars

Next ==
    \/ InitTree
    \/ \E n \in Nodes : BeginWait(n)
    \/ \E n \in Nodes, m \in Nodes : SendEcho(n, m)
    \/ \E m \in Nodes : AcceptEcho(m)
    \/ \E n \in Nodes : MarkDone(n)
    \/ Halt

AncestorProperties ==
    LET
        ancOf(n) == {n} \cup IF parent[n] = NoNode THEN {} ELSE ancOf(parent[n])
        isAncestor(a, n) == a \in ancOf(n)
    IN
        /\ (\A n \in done : n = initiator \/ (parent[n] # NoNode /\ isAncestor(initiator, n)))
        /\ (\A a, b \in Nodes : (isAncestor(a, b) /\ isAncestor(b, a)) => a = b)

TestSpec ==
    /\ InitState
    /\ [][Next]_vars

====