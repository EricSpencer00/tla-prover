---- MODULE MCEcho ----
EXTENDS Integers, Sequences

CONSTANTS Node, initiator, R, NoNode

N1 == Node
I1 == initiator
R1 == R

VARIABLES visited, parent, done

vars == <<visited, parent, done>>

Init ==
    /\ visited = [n \in N1 |-> IF n = I1 THEN "initiated" ELSE "idle"]
    /\ parent = [n \in N1 |-> NoNode]
    /\ done = FALSE

EchoStep(n) ==
    /\ visited[n] = "idle"
    /\ \E m \in N1 : m # n /\ visited[m] = "initiated"
    /\ visited' = [visited EXCEPT ![n] = "initiated"]
    /\ parent' = [parent EXCEPT ![n] = CHOOSE m \in N1 : m # n /\ visited[m] = "initiated"]
    /\ UNCHANGED done

EchoIdle ==
    /\ done = FALSE
    /\ \A n \in N1 : visited[n] = "initiated"
    /\ done' = TRUE
    /\ UNCHANGED <<visited, parent>>

Next ==
    \/ EchoIdle
    \/ \E n \in N1 : EchoStep(n)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ visited \in [N1 -> {"idle", "initiated"}]
    /\ parent \in [N1 -> N1 \cup {NoNode}]
    /\ done \in BOOLEAN

AncestorProperties ==
    /\ \A n \in N1 \ {I1} : parent[n] # NoNode
    /\ \A n \in N1 : (parent[n] # NoNode => parent[parent[n]] # NoNode) /\ (n = I1 => parent[n] = NoNode)

TestSpec ==
    /\ Spec
    /\ \A n \in N1, m \in N1 : (m \in R1 /\ n \in R1) => m # n
    /\ \E n \in N1 : \A m \in R1 : n \in R1 /\ m \in R1 => n # m
    /\ \A n \in N1, m \in R1 : (n \in R1 /\ m \in R1) => (n \in R1 <=> m \in R1)

====