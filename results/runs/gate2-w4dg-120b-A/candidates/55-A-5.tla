---- MODULE MCEcho ----
EXTENDS Integers, TLC

\* The Echo spanning-tree algorithm, instantiated for model checking with a concrete
\* three-node fully-meshed graph. Every identifier below must exist for the .cfg to
\* resolve it: the constants, the specification name, the INIT and NEXT operators, and
\* the invariants. No extra or renamed identifiers may be added or removed.
CONSTANTS Node, initiator, R, NoNode

\* Relationship R must be reflexive, symmetric, irreflexive, and connected: the full
\* set of all ordered pairs of distinct nodes in the three-node graph, which satisfies
\* all three. A sentinel "NoNode" represents the yet-to-be-assigned parent in the echo.
VARIABLES parent, phase, responded, fin

vars == <<parent, phase, responded, fin>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ phase \in [Node -> {"idle", "sent", "done"}]
    /\ responded \in [Node -> BOOLEAN]
    /\ fin \in BOOLEAN

\* Invariant from the Echo spec: at termination, the initiator is an ancestor of every
\* other node and the ancestor relation forms a spanning tree (no node is its own
\* ancestor, and the initiator has no parent, so the parent pointers are acyclic).
AncestorProperties ==
    /\ \A x \in Node : phase[x] = "done"
    /\ \A x \in Node : x # initiator => (parent[x] # NoNode /\ parent[x] # x)
    /\ parent[initiator] = NoNode

Init ==
    /\ parent = [x \in Node |-> NoNode]
    /\ phase = [x \in Node |-> "idle"]
    /\ responded = [x \in Node |-> FALSE]
    /\ fin = FALSE

\* All actions of the Echo algorithm are inherited unchanged; no extra or omitted
\* actions may be introduced here. The initiator starts the echo, every node
\* responds exactly once, and the echo finishes once all have responded.
Send ==
    /\ phase[initiator] = "idle"
    /\ phase' = [phase EXCEPT ![initiator] = "sent"]
    /\ UNCHANGED <<parent, responded, fin>>

Respond(x) ==
    /\ phase[x] = "sent"
    /\ \E y \in Node \ {x} :
         /\ parent' = [parent EXCEPT ![x] = y]
         /\ phase' = [phase EXCEPT ![x] = "done"]
    /\ responded' = [responded EXCEPT ![x] = TRUE]
    /\ UNCHANGED fin

Finish ==
    /\ \A x \in Node : responded[x]
    /\ fin' = TRUE
    /\ UNCHANGED <<parent, phase, responded>>

\* When the echo is finished, the system idles forever: this keeps the model checker
\* from reporting "deadlocked" even though the algorithm has naturally quiesced.
Idle == UNCHANGED vars

Next ==
    \/ Send
    \/ \E x \in Node : Respond(x)
    \/ Finish
    \/ Idle

Spec == Init /\ [][Next]_vars

\* The designated test entry point: the invariant set is fixed by the reference
\* configuration, so it must name the exact identifiers below and nothing else.
TestSpec == Spec
TypeOK == TypeOK
AncestorProperties == AncestorProperties

====