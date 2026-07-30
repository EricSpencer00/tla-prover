---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, done, tokens, phase

vars == <<parent, done, tokens, phase>>

States == {"idle", "active", "done"}

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ done = [n \in Node |-> FALSE]
    /\ tokens = [n \in Node |-> IF n = initiator THEN 1 ELSE 0]
    /\ phase = States[1]

Echo ==
    /\ phase = "idle"
    /\ phase' = "active"
    /\ UNCHANGED <<parent, done, tokens>>

SendToken(n, m) ==
    /\ phase = "active"
    /\ tokens[n] > 0
    /\ <<n, m>> \in R
    /\ n # m
    /\ parent[m] = NoNode
    /\ tokens' = [tokens EXCEPT ![n] = tokens[n] - 1, ![m] = tokens[m] + 1]
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ UNCHANGED <<done, phase>>

Respond(n, m) ==
    /\ phase = "active"
    /\ tokens[n] > 0
    /\ <<n, m>> \in R
    /\ n # m
    /\ parent[n] = m
    /\ tokens' = [tokens EXCEPT ![n] = tokens[n] - 1, ![m] = tokens[m] + 1]
    /\ UNCHANGED <<parent, done, phase>>

Deliver(n) ==
    /\ phase = "active"
    /\ tokens[n] > 0
    /\ n = initiator
    /\ done' = [done EXCEPT ![n] = TRUE]
    /\ tokens' = [tokens EXCEPT ![n] = tokens[n] - 1]
    /\ UNCHANGED <<parent, phase>>

Complete ==
    /\ phase = "active"
    /\ \A n \in Node : n # initiator => done[n]
    /\ phase' = "done"
    /\ UNCHANGED <<parent, done, tokens>>

Next ==
    \/ Echo
    \/ \E n, m \in Node : SendToken(n, m)
    \/ \E n, m \in Node : Respond(n, m)
    \/ \E n \in Node : Deliver(n)
    \/ Complete

TestSpec == Init /\ [][Next]_vars

Ancestors(n) == {m \in Node : parent[m] = n}
Descendants(n) == {m \in Node : parent[n] = m}

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ done \in [Node -> BOOLEAN]
    /\ tokens \in [Node -> 0 .. 2]
    /\ phase \in States

AncestorProperties ==
    /\ initiator \in Ancestors[NoNode]
    /\ \A n \in Node : initiator \in Ancestors[n]
    /\ \A n \in Node : n \notin Ancestors[n]
    /\ \A n \in Node : n \notin Descendants[n]

====