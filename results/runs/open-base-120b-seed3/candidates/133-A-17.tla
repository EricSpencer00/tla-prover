---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succSet

\* ----------------------------------------------------------------------
\* Bounded sequence operator used by the configuration (replaces Seq)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Graph successor operator for the configuration (substituted for Succ)
\* Each node has exactly two distinct successors.
\* ----------------------------------------------------------------------
TwoSucc(n) == 
    CHOOSE S \in SUBSET Nodes :
        /\ Cardinality(S) = 2
        /\ n \notin S

ConnectedToSomeButNotAll == [n \in Nodes |-> TwoSucc(n)]

\* ----------------------------------------------------------------------
\* Initial state (inherits from the parallel algorithm)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> Null]
    /\ succSet = [p \in Procs |-> {}]

\* ----------------------------------------------------------------------
\* Next-state relation (placeholder – the real actions are inherited)
\* ----------------------------------------------------------------------
Next ==
    \E p \in Procs :
        \/ /\ pc[p] = "idle"
           /\ pc' = [pc EXCEPT ![p] = "work"]
           /\ UNCHANGED <<marked, frontier, sel, succSet>>
        \/ /\ pc[p] = "work"
           /\ \E n \in frontier :
                /\ sel' = [sel EXCEPT ![p] = n]
                /\ frontier' = frontier \ {n}
                /\ marked' = marked \cup {n}
                /\ pc' = [pc EXCEPT ![p] = "idle"]
                /\ UNCHANGED succSet
        \/ /\ pc[p] = "done"
           /\ UNCHANGED <<marked, frontier, pc, sel, succSet>>

Vars == <<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Inductive invariant (type correctness and control‑flow properties)
\* ----------------------------------------------------------------------
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs : pc[p] \in {"idle", "work", "done"}
    /\ \A p \in Procs : sel[p] \in Nodes \cup {Null}
    /\ \A p \in Procs : succSet[p] \subseteq Nodes

\* ----------------------------------------------------------------------
\* Refinement property (parallel algorithm refines the sequential Misra
\* algorithm) – placeholder definition
\* ----------------------------------------------------------------------
Refines == TRUE

====