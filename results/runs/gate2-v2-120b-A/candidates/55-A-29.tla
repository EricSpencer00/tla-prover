---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants required by the reference configuration
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
NodeSet == Node
Vars    == << parent, sent, received >>

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES parent, sent, received

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Children(p) == { n \in NodeSet : parent[n] = p }

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
    /\ parent \in [NodeSet -> (NodeSet \cup {NoNode})]
    /\ sent   \in SUBSET R
    /\ received \in SUBSET R

\* ----------------------------------------------------------------------
\* Initial state (inherits Init from Echo specification)
\* ----------------------------------------------------------------------
Init ==
    /\ parent = [n \in NodeSet |-> NoNode]
    /\ sent   = {}
    /\ received = {}

\* ----------------------------------------------------------------------
\* Actions (inherit from Echo specification)
\* ----------------------------------------------------------------------
Send(u, v) ==
    /\ u \in NodeSet
    /\ v \in NodeSet
    /\ u # v
    /\ (u = initiator \/ parent[u] # NoNode)
    /\ parent[v] = NoNode
    /\ parent' = [parent EXCEPT ![v] = u]
    /\ sent'   = sent \cup {<<u, v>>}
    /\ UNCHANGED received

Recv(u, v) ==
    /\ u \in NodeSet
    /\ v \in NodeSet
    /\ u # v
    /\ <<v, u>> \in sent
    /\ <<v, u>> \notin received
    /\ received' = received \cup {<<v, u>>}
    /\ UNCHANGED <<parent, sent>>

EchoStep ==
    \/ \E u \in NodeSet, v \in NodeSet: Send(u, v)
    \/ \E u \in NodeSet, v \in NodeSet: Recv(u, v)

Next == EchoStep

\* ----------------------------------------------------------------------
\* Safety property: Ancestor (spanning‑tree) properties
\* ----------------------------------------------------------------------
AncestorProperties ==
    /\ initiator \in NodeSet
    /\ \A n \in NodeSet \ {initiator} :
          /\ parent[n] # NoNode
          /\ initiator \in ReachableFrom(n)
    /\ NoCycles

\* Reachability from a node following parent pointers
ReachableFrom(n) ==
    LET Rec(m) == IF m = NoNode THEN {} ELSE {m} \cup Rec(parent[m])
    IN Rec(n) \ {NoNode}

\* Acyclicity of the parent relation
NoCycles ==
    \A n \in NodeSet :
        initiator \notin RecChain(parent, n)

\* Helper to follow the parent chain (could loop forever, but used only
\* inside NoCycles where the graph is finite)
RecChain(rel, n) ==
    IF n = NoNode THEN {}
    ELSE {n} \cup RecChain(rel, rel[n])

\* ----------------------------------------------------------------------
\* Liveness property (not specified)
\* ----------------------------------------------------------------------
Liveness == TRUE

\* ----------------------------------------------------------------------
\* Specification and properties as required by the .cfg file
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<parent, sent, received>>

TestSpec == Spec

=============================================================================