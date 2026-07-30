---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* Echo is a spanning-tree broadcast measured against initiator reachability.
\* EchoSpec defines the actors, the message buffers, and every action; it
\* changes no constant, so the model is complete as long as it re-exports the
\* constants that the reference configuration expects.

CONSTANTS
    N == Cardinality(Node)
    Nodes == CHOOSE S \in SUBSET Node : S = Node

VARIABLES parent, status, inbox, discover, echoing

vars == <<parent, status, inbox, discover, echoing>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ status \in [Node -> {"idle", "discovering", "echoing", "done"}]
    /\ inbox \in [Node -> SUBSET (Node \X Node \X {"trig"})]
    /\ discover \in [Node -> 0..N]
    /\ echoing \subseteq Node

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ status = [n \in Node |-> IF n = initiator THEN "discovering" ELSE "idle"]
    /\ inbox = [n \in Node |-> {}]
    /\ discover = [n \in Node |-> 0]
    /\ echoing = {}

SendDiscover(a, b) ==
    /\ status[a] = "discovering"
    /\ \A m \in inbox[b] : m[1] # a
    /\ inbox' = [inbox EXCEPT ![b] = @ \cup {<<a, b, "trig">>}]
    /\ UNCHANGED <<parent, status, discover, echoing>>

ReceiveDiscover(n, m) ==
    /\ status[n] = "idle"
    /\ m \in inbox[n]
    /\ parent' = [parent EXCEPT ![n] = m[1]]
    /\ inbox' = [inbox EXCEPT ![n] = @ \ {m}]
    /\ status' = [status EXCEPT ![n] = "discovering"]
    /\ UNCHANGED <<discover, echoing>>

Echo(n) ==
    /\ status[n] = "discovering"
    /\ parent[n] # initiator
    /\ discover[n] < N
    /\ status' = [status EXCEPT ![n] = "echoing"]
    /\ discover' = [discover EXCEPT ![n] = @ + 1]
    /\ echoing' = echoing \cup {n}
    /\ inbox' = [inbox EXCEPT ![parent[n]] = @ \cup {<<n, parent[n], "trig">>}]
    /\ UNCHANGED parent

Terminate(n) ==
    /\ status[n] = "discovering"
    /\ parent[n] = initiator
    /\ discover[n] < N
    /\ status' = [status EXCEPT ![n] = "echoing"]
    /\ discover' = [discover EXCEPT ![n] = @ + 1]
    /\ echoing' = echoing \cup {n}
    /\ UNCHANGED <<parent, inbox>>

Complete ==
    /\ \A n \in Node : status[n] = "echoing" \/ status[n] = "done"
    /\ status' = [n \in Node |->
                     IF status[n] = "echoing" THEN "done" ELSE status[n]]
    /\ UNCHANGED <<parent, inbox, discover, echoing>>

Next ==
    \/ Complete
    \/ \E a, b \in Node : SendDiscover(a, b)
    \/ \E n \in Node, m \in inbox[n] : ReceiveDiscover(n, m)
    \/ \E n \in Node : Echo(n) \/ Terminate(n)

Spec == Init /\ [][Next]_vars

AncestorProperties ==
    /\ initiator \in Node
    /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => parent[n] \in Node

TestSpec ==
    /\ Spec
    /\ \A n \in Node : /\ Cardinality({m \in Node : parent[m] = n}) =< 1
                       /\ parent[initiator] = NoNode
====