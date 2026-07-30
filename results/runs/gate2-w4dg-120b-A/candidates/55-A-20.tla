---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, initiator, R, NoNode

Nodes == {"n1", "n2", "n3"}

VARIABLES active, parent, level, acked

vars == <<active, parent, level, acked>>

InitState ==
    /\ active = [n \in Nodes |-> IF n = initiator THEN "active" ELSE "idle"]
    /\ parent = [n \in Nodes |-> NoNode]
    /\ level  = [n \in Nodes |-> IF n = initiator THEN 0 ELSE 0]
    /\ acked  = [n \in Nodes |-> "none"]

Init ==
    /\ active = InitState.active
    /\ parent = InitState.parent
    /\ level  = InitState.level
    /\ acked  = InitState.acked

Wake(n, m) ==
    /\ active[n] = "idle"
    /\ parent[n] = NoNode
    /\ active[m] = "active"
    /\ n # m
    /\ active' = [active EXCEPT ![n] = "active"]
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ level'  = [level  EXCEPT ![n] = level[m] + 1]
    /\ UNCHANGED <<acked>>

Ack(n) ==
    /\ active[n] = "active"
    /\ parent[n] # NoNode
    /\ acked' = [acked EXCEPT ![n] = "done"]
    /\ UNCHANGED <<active, parent, level>>

Sleep(n) ==
    /\ active[n] = "active"
    /\ parent[n] = NoNode
    /\ n # initiator
    /\ active' = [active EXCEPT ![n] = "idle"]
    /\ UNCHANGED <<parent, level, acked>>

Quiet ==
    /\ \A n \in Nodes : ~ (active[n] = "active" /\ parent[n] # NoNode)
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Nodes, m \in Nodes : Wake(n, m)
    \/ \E n \in Nodes : Ack(n)
    \/ \E n \in Nodes : Sleep(n)
    \/ Quiet

Spec ==
    /\ Init
    /\ [][Next]_vars

PrintAdjacency ==
    /\ ~ \A m : m \in Nodes
    /\ (\A m \in Nodes : m \in Nodes)
    /\ TRUE

TestSpec ==
    /\ Spec
    /\ PrintAdjacency

TypeOK ==
    /\ active \in [Nodes -> {"idle", "active"}]
    /\ parent \in [Nodes -> Nodes \cup {NoNode}]
    /\ level  \in [Nodes -> Nat]
    /\ acked  \in [Nodes -> {"none", "done"}]

AncestorProperties ==
    /\ \A n \in Nodes \ {initiator} : parent[n] # NoNode
    /\ \A n \in Nodes \ {initiator} : active[n] = "active"
    /\ \A n \in Nodes : InitiatorAncestor(n)
    /\ \A n \in Nodes : NoCycle(n)

InitiatorAncestor(n) ==
    (n = initiator) \/ (parent[n] # NoNode /\ InitiatorAncestor(parent[n]))

NoCycle(n) ==
    (parent[n] # NoNode) => (parent[n] # n /\ NoCycle(parent[n]))

====