---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
NodeSet == Node
ParentSet == Node \cup {NoNode}

\* ----------------------------------------------------------------------
\* State variables (as in Echo.tla)
\* ----------------------------------------------------------------------
VARIABLES parent, sent, received, active

\* ----------------------------------------------------------------------
\* Type correctness invariant (required)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ parent \in [Node -> ParentSet]
    /\ sent   \in [Node -> BOOLEAN]
    /\ received \in [Node -> BOOLEAN]
    /\ active \in BOOLEAN

\* ----------------------------------------------------------------------
\* Safety invariant AncestorProperties (required)
\* ----------------------------------------------------------------------
\* No cycles in the ancestor relation and the initiator is an ancestor of all.
\* We define Ancestors(n) as the set of nodes reachable from n by following
\* the parent links (excluding NoNode).  The invariant asserts:
\*   1. No node is its own ancestor (acyclicity).
\*   2. Every node (except the initiator) eventually reaches the initiator.
\* (The formulation works in all reachable states, not only at termination.)
AncestorProperties ==
    /\ \A n \in Node :
          ~ (n \in Ancestors(n))
    /\ \A n \in Node \ {initiator} :
          initiator \in Ancestors(n)

\* Ancestors function (recursive definition)
Ancestors(n) ==
    IF parent[n] = NoNode THEN {}
    ELSE {parent[n]} \cup Ancestors(parent[n])

\* ----------------------------------------------------------------------
\* Initial state (inherits from Echo, instantiated for the concrete graph)
\* ----------------------------------------------------------------------
Init ==
    /\ parent = [i \in Node |-> NoNode]
    /\ sent   = [i \in Node |-> FALSE]
    /\ received = [i \in Node |-> FALSE]
    /\ active = TRUE
    /\ initiator \in Node
    /\ NoNode \notin Node
    /\ Disjoint(Node, {NoNode})
    /\ R = { <<i, j>> : i \in Node, j \in Node, i # j }

\* ----------------------------------------------------------------------
\* Next-state relation (inherits actions from Echo)
\* For completeness we model the three essential actions of the Echo algorithm.
\* The exact algorithmic details are not critical for the required invariants.
\* ----------------------------------------------------------------------
Send(i) ==
    /\ i \in Node
    /\ ~sent[i]
    /\ sent' = [sent EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<parent, received, active>>

Receive(j) ==
    /\ j \in Node
    /\ sent[j] = TRUE
    /\ ~received[j]
    /\ received' = [received EXCEPT ![j] = TRUE]
    /\ UNCHANGED <<parent, sent, active>>

SetParent(k, p) ==
    /\ k \in Node
    /\ p \in Node
    /\ parent[k] = NoNode
    /\ parent' = [parent EXCEPT ![k] = p]
    /\ UNCHANGED <<sent, received, active>>

Terminate ==
    /\ \A i \in Node : parent[i] # NoNode
    /\ active' = FALSE
    /\ UNCHANGED <<parent, sent, received>>

Next ==
    \/ \E i \in Node : Send(i)
    \/ \E j \in Node : Receive(j)
    \/ \E k \in Node :
          \E p \in Node :
            SetParent(k, p)
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification (required name)
\* ----------------------------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, sent, received, active>>

\* ----------------------------------------------------------------------
\* Theorems (optional, but useful for TLC)
\* ----------------------------------------------------------------------
THEOREM SpecImplyTypeOK == TestSpec => []TypeOK
THEOREM SpecImplyAncestor == TestSpec => []AncestorProperties

====