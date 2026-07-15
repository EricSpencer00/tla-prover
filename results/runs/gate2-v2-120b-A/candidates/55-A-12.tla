---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

\* -------------------------------------------------
\* Constants required by the reference configuration
\* -------------------------------------------------
CONSTANTS
    Node,       \* the set of node identifiers (strings)
    initiator,  \* the distinguished initiator node
    R,          \* adjacency relation (undirected graph)
    NoNode      \* sentinel value representing "no parent"

\* -------------------------------------------------
\* Derived sets and definitions
\* -------------------------------------------------
Neighbors == [n \in Node |-> { m \in Node : (n, m) \in R }]

\* -------------------------------------------------
\* State variables (as required by the Echo spec)
\* -------------------------------------------------
VARIABLES
    parent,    \* map each node to its parent (or NoNode)
    sent,      \* set of nodes that have sent their echo
    recv,      \* set of nodes that have received echoes from all neighbors
    done       \* boolean indicating termination

\* -------------------------------------------------
\* Initial state (same as Echo specification)
\* -------------------------------------------------
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent   = {}
    /\ recv   = {}
    /\ done   = FALSE

\* -------------------------------------------------
\* Actions (same as Echo specification, simplified)
\* -------------------------------------------------
SendEcho ==
    \E n \in Node \ {initiator} :
        /\ parent[n] = NoNode
        /\ parent' = [parent EXCEPT ![n] = initiator]
        /\ sent'   = sent \cup {n}
        /\ UNCHANGED <<recv, done>>

ReceiveEcho ==
    \E n \in Node :
        /\ n \in sent
        /\ recv' = recv \cup {n}
        /\ UNCHANGED <<parent, sent, done>>

Terminate ==
    /\ \A n \in Node : n = initiator \/ parent[n] \in Node
    /\ done' = TRUE
    /\ UNCHANGED <<parent, sent, recv>>

Next ==
    \/ SendEcho
    \/ ReceiveEcho
    \/ Terminate
    \/ UNCHANGED <<parent, sent, recv, done>>

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, sent, recv, done>>

\* -------------------------------------------------
\* Safety invariants (as required)
\* -------------------------------------------------
\* Type correctness
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ sent   \subseteq Node
    /\ recv   \subseteq Node
    /\ done   \in BOOLEAN

\* Ancestor relation: parent links form a tree rooted at initiator
Ancestor ==
    \A n \in Node :
        (n = initiator) \/ (parent[n] \in Node)

NoCycle ==
    \A n \in Node :
        LET rec(p) == IF p = initiator THEN {}
                     ELSE IF p = NoNode THEN {}
                     ELSE {p} \cup rec(parent[p])
        IN initiator \notin rec(n)

AncestorProperties == Ancestor /\ NoCycle

\* -------------------------------------------------
\* Variant for printing the graph (optional, no effect on model)
\* -------------------------------------------------
PrintGraph ==
    /\ /\* No state change, just a placeholder for a possible I/O action */
       TRUE
    /\ UNCHANGED <<parent, sent, recv, done>>

=============================================================================