---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Node, initiator, R, NoNode

\* Derived constant: the set of all nodes
NodeSet == Node

\* State variables inherited from the Echo specification
VARIABLES parent, received

\* ----------------------------------------------------------------------
\* Type predicates
\* ----------------------------------------------------------------------
NodeOrNoNode(x) == x \in NodeSet \/ x = NoNode
ParentOk(p) == \A n \in NodeSet: p[n] \in NodeOrNoNode

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ parent = [n \in NodeSet |-> NoNode]
    /\ received = [n \in NodeSet |-> FALSE]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Neighbors(n) == { m \in NodeSet : (n, m) \in R }

\* ----------------------------------------------------------------------
\* Actions (a faithful copy of the Echo algorithm)
\* ----------------------------------------------------------------------
Send(n, m) ==
    /\ n \in NodeSet
    /\ m \in Neighbors(n)
    /\ parent[n] = NoNode
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ UNCHANGED received

Receive(m) ==
    /\ m \in NodeSet
    /\ \E n \in Neighbors(m) : parent[n] = m
    /\ received' = [received EXCEPT ![m] = TRUE]
    /\ UNCHANGED parent

Terminate ==
    /\ received = [n \in NodeSet |-> TRUE]
    /\ UNCHANGED <<parent, received>>

Next ==
    \/ \E n, m \in NodeSet: Send(n, m)
    \/ \E m \in NodeSet: Receive(m)
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, received>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK == /\ ParentOk(parent)
          /\ \A n \in NodeSet: received[n] \in BOOLEAN

\* Ancestor relation (transitive closure of parent links)
Ancestor(a, b) ==
    /\ a \in NodeSet
    /\ b \in NodeSet
    /\ b # a
    /\ \E n \in NodeSet: 
        /\ parent[n] = a
        /\ (n = b \/ Ancestor(n, b))

\* Ancestor properties required by the Echo spec
AncestorProperties ==
    /\ TERMINATED /\ received = [n \in NodeSet |-> TRUE] => 
        /\ initiator \in NodeSet
        /\ \A n \in NodeSet: n = initiator \/ Ancestor(initiator, n)
        /\ \A a, b \in NodeSet: 
            Ancestor(a, b) => ~Ancestor(b, a)   \* acyclicity

\* ----------------------------------------------------------------------
\* Termination flag for the AncestorProperties invariant
\* ----------------------------------------------------------------------
TERMINATED == received = [n \in NodeSet |-> TRUE]

\* ----------------------------------------------------------------------
\* Proof obligations (optional, can be omitted in the final module)
\* ----------------------------------------------------------------------
(*
THEOREM InitImpliesTypeOK == Init => TypeOK

THEOREM SpecImpliesTypeOK == TestSpec => []TypeOK
*)

====