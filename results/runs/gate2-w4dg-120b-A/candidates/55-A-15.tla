---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

Node == {"n1", "n2", "n3"}

VARIABLES total, reqs, parent, done

vars == <<total, reqs, parent, done>>

TypeOK ==
    /\ total \in [Node -> 0..2]
    /\ reqs \subseteq Node
    /\ parent \in [Node -> Node \cup {"NoNode"}]
    /\ done \in BOOLEAN

Init ==
    /\ total = [n \in Node |-> 0]
    /\ reqs = {}
    /\ parent = [n \in Node |-> "NoNode"]
    /\ done = FALSE

StartEcho ==
    /\ reqs = {}
    /\ reqs' = {initiator}
    /\ total' = [total EXCEPT ![initiator] = 1]
    /\ UNCHANGED <<parent, done>>

InitMsg(n, m) ==
    /\ n \in reqs
    /\ m \notin reqs
    /\ parent[m] = "NoNode"
    /\ reqs' = reqs \cup {m}
    /\ total' = [total EXCEPT ![m] = total[n] + 1]
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ UNCHANGED done

DoneMsg(n) ==
    /\ n \in reqs
    /\ parent[n] # "NoNode"
    /\ done' = TRUE
    /\ UNCHANGED <<total, reqs, parent>>

EchoStep == StartEcho \/ \E n \in Node, m \in Node : InitMsg(n, m) \/ DoneMsg(n)

Next == EchoStep

TestSpec == EchoStep

AncestorProperties ==
    /\ \A n \in Node : n # initiator => parent[n] # "NoNode"
    /\ \A n \in Node : (n # initiator /\ parent[n] # "NoNode") ~> (parent[parent[n]] # "NoNode")
====