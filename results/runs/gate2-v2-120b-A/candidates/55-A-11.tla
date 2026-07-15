---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

\* ------------------------------------------------------------
\* Constants required by the reference configuration
\* ------------------------------------------------------------
CONSTANTS
    Node,        \* the set of node identifiers
    initiator,   \* the distinguished initiator node
    R,           \* the undirected adjacency relation (set of unordered pairs)
    NoNode       \* a sentinel value distinct from all nodes, meaning "no parent"

\* ------------------------------------------------------------
\* Derived constants
\* ------------------------------------------------------------
Nodes == Node

\* ------------------------------------------------------------
\* Variables (inherited from the Echo specification)
\* ------------------------------------------------------------
VARIABLES
    parent,      \* [n \in Nodes |-> NoNode] initially; later a node or NoNode
    sent,        \* [n \in Nodes |-> FALSE] initially; becomes TRUE when n has sent its echo
    received,    \* [n \in Nodes |-> {}] initially; set of neighbors from which n has received echoes
    done         \* [n \in Nodes |-> FALSE] initially; TRUE when n has completed its part

\* ------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------
Neighbors == [n \in Nodes |-> { m \in Nodes : {n,m} \in R }]

\* ------------------------------------------------------------
\* Initial state (inherits Echo's INIT, instantiated for this graph)
\* ------------------------------------------------------------
Init ==
    /\ parent = [n \in Nodes |-> NoNode]
    /\ sent   = [n \in Nodes |-> FALSE]
    /\ received = [n \in Nodes |-> {}]
    /\ done = [n \in Nodes |-> FALSE]
    /\ sent[initiator] = TRUE
    /\ parent[initiator] = initiator

\* ------------------------------------------------------------
\* Actions (inherits Echo's NEXT, instantiated)
\* ------------------------------------------------------------
SendEcho ==
    \E n \in Nodes :
        /\ ~sent[n]
        /\ \A m \in Neighbors[n] : ~sent[m]    \* can only send when neighbors haven't sent yet
        /\ sent' = [sent EXCEPT ![n] = TRUE]
        /\ UNCHANGED <<parent, received, done>>

ReceiveEcho ==
    \E n \in Nodes :
        \E m \in Neighbors[n] :
            /\ sent[m]
            /\ m \notin received[n]
            /\ received' = [received EXCEPT ![n] = @ \cup {m}]
            /\ UNCHANGED <<parent, sent, done>>

SetParent ==
    \E n \in Nodes :
        /\ parent[n] = NoNode
        /\ \E m \in received[n] :
            /\ parent' = [parent EXCEPT ![n] = m]
            /\ UNCHANGED <<sent, received, done>>

Terminate ==
    \E n \in Nodes :
        /\ ~done[n]
        /\ \A m \in Neighbors[n] : m \in received[n] \cup {parent[n]}
        /\ done' = [done EXCEPT ![n] = TRUE]
        /\ UNCHANGED <<parent, sent, received>>

Next ==
    \/ SendEcho
    \/ ReceiveEcho
    \/ SetParent
    \/ Terminate

\* ------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, sent, received, done>>

\* ------------------------------------------------------------
\* Invariants
\* ------------------------------------------------------------
\* Type correctness
TypeOK ==
    /\ parent \in [Nodes -> NoNode \cup Nodes]
    /\ sent \in [Nodes -> BOOLEAN]
    /\ received \in [Nodes -> SUBSET Nodes]
    /\ done \in [Nodes -> BOOLEAN]
    /\ initiator \in Nodes
    /\ NoNode \notin Nodes
    /\ NoNode \notin UNION R
    /\ initiator \in Nodes

\* Ancestor (spanning tree) properties
AncestorProperties ==
    /\ \A n \in Nodes : (parent[n] = NoNode) => (n = initiator)
    /\ \A n \in Nodes : (parent[n] # NoNode) => (parent[n] \in Nodes)
    /\ \A n \in Nodes : n = initiator => (parent[n] = initiator)
    /\ \A n \in Nodes : n # initiator => (n \in DOMAIN parent)
    /\ \A n \in Nodes : n # initiator => (parent[n] # NoNode)
    /\ NoCycles
\* NoCycles ensures the parent relation is acyclic
NoCycles ==
    \A n \in Nodes :
        ~(\E k \in Nat :
            k > 0 /\ 
            Let seq == [i \in 0..k |-> 
                IF i = 0 THEN n ELSE parent[seq[i-1]] ] IN
            /\ \A i \in 1..k : seq[i] # NoNode
            /\ seq[k] = n)

\* ------------------------------------------------------------
\* Theorem (optional, for TLC checking)
\* ------------------------------------------------------------
THEOREM SpecImpliesSafety == TestSpec => []TypeOK /\ []AncestorProperties

====