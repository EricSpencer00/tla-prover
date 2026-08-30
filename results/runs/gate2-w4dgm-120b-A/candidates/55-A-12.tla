---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Node, initiator, R, NoNode

\* A fully-meshed three-node graph: every distinct ordered pair is a link.
Link == {<<x, y>> \in Node \X Node : x # y}

VARIABLES mode, phase, parent, init, recv, acked

vars == <<mode, phase, parent, init, recv, acked>>

InitMode == [n \in Node |-> IF n = initiator THEN "initiate" ELSE "idle"]
AckCount == Cardinality({n \in Node : mode[n] = "acknowledge"})

TypeOK ==
    /\ mode \in [Node -> {"idle", "initiate", "awaiting", "echo", "acknowledge"}]
    /\ phase \in [Node -> {"idle", "active", "done"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ init \in [Node -> Subset(R)]
    /\ recv \in [Node -> Seq(R)]
    /\ acked \in [Node -> BOOLEAN]

Init ==
    /\ mode = InitMode
    /\ phase = [n \in Node |-> IF n = initiator THEN "active" ELSE "idle"]
    /\ parent = [n \in Node |-> NoNode]
    /\ init = [n \in Node |-> IF n = initiator THEN R ELSE {}]
    /\ recv = [n \in Node |-> << >>]
    /\ acked = [n \in Node |-> FALSE]

Activate ==
    /\ \E x \in Node:
         /\ mode[x] = "initiate"
         /\ mode' = [mode EXCEPT ![x] = "awaiting"]
    /\ UNCHANGED <<phase, parent, init, recv, acked>>

SendEcho ==
    /\ \E x \in Node, y \in Node:
         /\ mode[x] = "awaiting"
         /\ <<x, y>> \in Link
         /\ phase[y] = "idle"
         /\ init[y] = {}
         /\ init' = [init EXCEPT ![y] = init[x]]
         /\ mode' = [mode EXCEPT ![x] = "active", ![y] = "echo"]
         /\ phase' = [phase EXCEPT ![y] = "active"]
         /\ parent' = [parent EXCEPT ![y] = x]
    /\ UNCHANGED <<recv, acked>>

RelayedEcho ==
    /\ \E x \in Node, y \in Node:
         /\ mode[x] \in {"awaiting", "echo"}
         /\ <<x, y>> \in Link
         /\ phase[y] = "idle"
         /\ parent[y] = NoNode
         /\ init[y] = {}
         /\ init' = [init EXCEPT ![y] = init[x]]
         /\ mode' = [mode EXCEPT ![y] = "echo"]
         /\ phase' = [phase EXCEPT ![y] = "active"]
         /\ parent' = [parent EXCEPT ![y] = x]
    /\ UNCHANGED <<recv, acked>>

Receive ==
    /\ \E x \in Node, e \in init[x]:
         /\ phase[x] = "active"
         /\ recv' = [recv EXCEPT ![x] = Append(@, e)]
         /\ init' = [init EXCEPT ![x] = init[x] \ {e}]
    /\ UNCHANGED <<mode, phase, parent, acked>>

Acknowledge ==
    /\ \E x \in Node:
         /\ mode[x] = "active"
         /\ mode' = [mode EXCEPT ![x] = "acknowledge"]
    /\ UNCHANGED <<phase, parent, init, recv, acked>>

RelayAcknowledge ==
    /\ \E x \in Node:
         /\ mode[x] = "acknowledge"
         /\ parent[x] # NoNode
         /\ mode[parent[x]] # "acknowledge"
         /\ mode' = [mode EXCEPT ![parent[x]] = "acknowledge"]
    /\ UNCHANGED <<phase, parent, init, recv, acked>>

Finish ==
    /\ AckCount = Cardinality(Node)
    /\ \A x \in Node: phase[x] = "idle" \/ phase[x] = "done"
    /\ UNCHANGED vars

Next ==
    \/ Activate \/ SendEcho \/ RelayedEcho \/ Receive
    \/ Acknowledge \/ RelayAcknowledge \/ Finish

Spec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ \A x \in Node: parent[x] # NoNode => (parent[parent[x]] # x /\ phase[parent[x]] = "done")
    /\ \A x \in Node: phase[x] = "done" => parent[x] # NoNode

\* Test-only: dump the fully-meshed graph's adjacency to stdout at startup.
PrintGraph ==
    /\ \A x \in Node: \A y \in Node: x # y => <<x, y>> \in Link
    /\ \E p \in Node, q \in Node: p # q => <<p, q>> \in Link
    /\ UNCHANGED vars

TestSpec == Spec /\ PrintGraph

====