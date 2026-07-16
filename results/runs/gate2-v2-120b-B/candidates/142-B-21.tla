-------------------------- MODULE ReachableProofs --------------------------
EXTENDS Reachable, ReachabilityProofs, TLAPS

VARIABLES marked, vroot, pc

\* -------------------------------------------------------------------------
\* Constants required by the underlying modules
\* -------------------------------------------------------------------------
CONSTANTS Nodes, Succ, Root

\* -------------------------------------------------------------------------
\* Type correctness (kept unchanged)
\* -------------------------------------------------------------------------
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ vroot  \in SUBSET Nodes
    /\ pc \in {"a", "Done"}
    /\ pc = "Done" => vroot = {}

\* -------------------------------------------------------------------------
\* Invariant Inv1 from module Reachable (kept unchanged)
\* -------------------------------------------------------------------------
Inv1 ==
    /\ pc = "Done" => vroot = {}
    /\ marked \subseteq Reachable

\* -------------------------------------------------------------------------
\* Invariant Inv2 from module Reachable (kept unchanged)
\* -------------------------------------------------------------------------
Inv2 ==
    /\ marked \cup vroot = Reachable

\* -------------------------------------------------------------------------
\* Invariant Inv3 from module Reachable (kept unchanged)
\* -------------------------------------------------------------------------
Inv3 ==
    Reachable = marked \cup ReachableFrom(vroot)

\* -------------------------------------------------------------------------
\* Initial state
\* -------------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ vroot  = {Root}
    /\ pc = "a"
    /\ TypeOK

\* -------------------------------------------------------------------------
\* Next-state relation
\* -------------------------------------------------------------------------
Next ==
    \E v \in vroot :
        IF v \notin marked THEN
            /\ marked' = marked \cup {v}
            /\ vroot'  = vroot \cup Succ[v]
            /\ pc'     = "a"
        ELSE
            /\ marked' = marked
            /\ vroot'  = vroot \ {v}
            /\ pc'     = "a"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, vroot, pc>>

vars == <<marked, vroot, pc>>

\* -------------------------------------------------------------------------
\* Specification
\* -------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

=============================================================================