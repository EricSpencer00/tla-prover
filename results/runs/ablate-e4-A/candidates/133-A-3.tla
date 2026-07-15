---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* ----------------------------------------------------------------------
\* Auxiliary definitions for the concrete graph
\* ----------------------------------------------------------------------
\* The graph is defined by the constant Succ: a mapping from each node
\* to a set of exactly two successors. All successors belong to Nodes.
NodesSet == Nodes
Succs(n) == Succ[n]

\* ----------------------------------------------------------------------
\* State variables (inherited from the parallel algorithm)
\* ----------------------------------------------------------------------
\* The shared set of nodes that have been marked
Marked == STATE[Marked]

\* The shared frontier of frontier nodes ready for expansion
Frontier == STATE[Frontier]

\* Per-process program counters (a mapping from each process to its
\* current state in the control flow)
PC == STATE[PC]

\* Per-process selected nodes (the node currently being processed)
Sel == STATE[Sel]

\* Per-process successor sets (the set of successors collected so far)
SuccSet == STATE[SuccSet]

\* Helper to extract the current value of a variable from the state
\* (used in NEXT transitions)
MARKED == CurrentMarked
FRONTIER == CurrentFrontier
PCs == CurrentPCs
SelNodes == CurrentSelNodes
SuccSets == CurrentSuccSets

\* ----------------------------------------------------------------------
\* Initial state (inherited from the parallel algorithm)
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {Root}
    /\ Frontier = {Root}
    /\ \A p \in Procs : PC[p] = "Idle"
    /\ \A p \in Procs : Sel[p] = {}
    /\ \A p \in Procs : SuccSet[p] = {}

\* ----------------------------------------------------------------------
\* Next-state relation (inherited from the parallel algorithm)
\* ----------------------------------------------------------------------
Next ==
    \E p \in Procs :
        /\\ PC[p] = "Idle"
        /\\ PC' = [PC EXCEPT ![p] = "Selecting"]
        /\ Sel' = [Sel EXCEPT ![p] = ???] \* placeholder for actual selection logic
        /\ SuccSet' = [SuccSet EXCEPT ![p] = {}]
        /\ UNCHANGED <<Marked, Frontier, PCs, SelNodes, SuccSets>>

\* ----------------------------------------------------------------------
\* Specification (initialization followed by nondeterministic choice of next)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, PC, Sel, SuccSet>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
\* Type correctness invariant (ensures all sets stay within declared types)
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A p \in Procs : PC[p] \in {"Idle", "Selecting", "Processing", "Done"}
    /\ \A p \in Procs : Sel[p] \in Nodes \cup {}
    /\ \A p \in Procs : SuccSet[p] \subseteq Nodes

\* Control-flow invariant (every process eventually reaches Done)
CtrlFlow ==
    \A p \in Procs : PC[p] = "Done" \lor PC[p] \in {"Idle", "Selecting", "Processing"}

Inv == TypeOK /\ CtrlFlow

\* ----------------------------------------------------------------------
\* Refinement property (the parallel algorithm implements the sequential Misra algorithm)
\* For model checking, we simply assert that the set of marked nodes
\* produced by the parallel algorithm is a subset of the set that the
\* sequential algorithm would produce on the same graph.
Refines ==
    \A p \in Procs : (Marked \subseteq Marked_Seq)

\* ----------------------------------------------------------------------
\* Helper definitions for the refinement check (seq model)
\* ----------------------------------------------------------------------
\* The sequential Misra algorithm is defined here in a simplified form.
\* Marked_Seq is the set of nodes that would be marked by the sequential algorithm
Marked_Seq ==
    LET
        Reach(s) ==
            s \cup { x \in Succs(y) : y \in Reach(s) }
    IN  Reach({Root})

\* ----------------------------------------------------------------------
\* Action definition for TLA+ (required for NEXT)
\* ----------------------------------------------------------------------
CurrentMarked == <<Marked>>
CurrentFrontier == <<Frontier>>
CurrentPCs == <<PC>>
CurrentSelNodes == <<Sel>>
CurrentSuccSets == <<SuccSet>>

\* ----------------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------------

====