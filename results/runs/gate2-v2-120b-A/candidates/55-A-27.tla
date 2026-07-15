---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

\*--- Constants (to be set in the .cfg) ---------------------------------
CONSTANT Node      \* The set of nodes (three string-valued nodes)
CONSTANT initiator \* The initiator node, element of Node
CONSTANT R         \* Undirected adjacency relation, subset of Node \X Node
CONSTANT NoNode    \* Sentinel value distinct from all nodes (used as "no parent")

\*--- Derived sets --------------------------------------------------------
Neighbors == [n \in Node |-> { m \in Node : <<n, m>> \in R }]

\*--- State variables (as in the Echo specification) --------------------
VARIABLES parent, active, done, received

vars == << parent, active, done, received >>

\*--- Initialization -------------------------------------------------------
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ active = {initiator}
    /\ done   = {}
    /\ received = {}

\*--- Helper definitions ---------------------------------------------------
Messages == {<<src, dst>> : <<src, dst>> \in R}
Sendable(msg) ==
    LET src == msg[1] IN
    LET dst == msg[2] IN
        /\ src \in active
        /\ dst \in Node \ {src}
        /\ msg \in Messages

\*--- Actions --------------------------------------------------------------
Send ==
    \E msg \in Messages :
        /\ Sendable(msg)
        /\ LET src == msg[1] IN
           LET dst == msg[2] IN
           /\ active' = active \ {src}
           /\ active' = active' \cup {dst}
           /\ parent' = [parent EXCEPT ![dst] = src]
           /\ UNCHANGED << done, received >>

Receive ==
    /\ active = {}
    /\ UNCHANGED vars

Next ==
    \/ Send
    \/ Receive

\*--- Specification ---------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--- Safety invariants ----------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ active \subseteq Node
    /\ done   \subseteq Node
    /\ received \subseteq SUBSET Node

\* Ancestor relationship (acyclic and initiator is ancestor of all)
Ancestor == [n \in Node |-> IF parent[n] = NoNode THEN {} ELSE {parent[n]} \cup Ancestor[parent[n]]]

AncestorProperties ==
    /\ \A n \in Node : initiator \in Ancestor[n] \/ n = initiator
    /\ \A n \in Node : initiator \notin Ancestor[initiator]  \* initiator has no ancestors
    /\ \A n \in Node : n \notin Ancestor[n]                 \* acyclicity

\*--- Test harness ---------------------------------------------------------
TestSpec ==
    /\ Spec
    /\ PrintLn("Adjacency relation R = " .. ToString(R))

\*--- Theorem (optional, helps TLC) ----------------------------------------
THEOREM Spec => []TypeOK /\ []AncestorProperties

=============================================================================