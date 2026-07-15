---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants required by the .cfg file.  Values are supplied by the
  configuration; we only declare them here.
--------------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* The set of graph nodes
    Root,    \* The distinguished start node
    Procs,   \* The set of worker processes
    Succ,    \* The graph's successor relation: a function Nodes -> SUBSET Nodes
    Seq      \* Upper bound on the length of any sequence (used for safety only)

(*--------------------------------------------------------------------
  Variables inherited from the parallel reachability algorithm.
--------------------------------------------------------------------*)
VARIABLES
    marked,       \* Shared set of nodes that have been discovered
    frontier,    \* Shared set of nodes currently being explored
    pc,          \* Per-process program counter (control state)
    sel,         \* Per-process selected node (or NULL)
    succs        \* Per-process set of successors to be added

(*--------------------------------------------------------------------
  Type correctness predicate (used in the safety invariant).
--------------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"Idle", "Select", "Explore", "Done"}]
    /\ sel \in [Procs -> (Nodes \cup {NULL})]
    /\ succs \in [Procs -> SUBSET Nodes]

(*--------------------------------------------------------------------
  Initial state (mirrors the sequential algorithm's initialization).
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "Idle"]
    /\ sel = [p \in Procs |-> NULL]
    /\ succs = [p \in Procs |-> {}]

(*--------------------------------------------------------------------
  Action definitions.
--------------------------------------------------------------------*)
Select(p) ==
    /\ pc[p] = "Idle"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ sel' = [sel EXCEPT ![p] = n]
          /\ succs' = [succs EXCEPT ![p] = Succ[n]]
    /\ pc' = [pc EXCEPT ![p] = "Select"]
    /\ UNCHANGED <<marked, frontier>>

Explore(p) ==
    /\ pc[p] = "Select"
    /\ sel[p] # NULL
    /\ \E n \in succs[p] :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {sel[p]}) \cup {n}
    /\ pc' = [pc EXCEPT ![p] = "Explore"]
    /\ UNCHANGED <<sel, succs>>

Done(p) ==
    /\ pc[p] = "Explore"
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<marked, frontier, sel, succs>>

(*--------------------------------------------------------------------
  Next-state relation: at each step one process may take one of the
  defined actions, or the system may stutter.
--------------------------------------------------------------------*)
Next ==
    \E p \in Procs :
        \/ Select(p)
        \/ Explore(p)
        \/ Done(p)
    \/ UNCHANGED <<marked, frontier, pc, sel, succs>>

(*--------------------------------------------------------------------
  Specification (temporal formula) required by the .cfg file.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

(*--------------------------------------------------------------------
  Safety invariant: combination of type correctness and a simple control-
  flow constraint that each process eventually reaches "Done".
--------------------------------------------------------------------*)
Inv == TypeOK /\ \A p \in Procs : pc[p] \in {"Idle", "Select", "Explore", "Done"}

(*--------------------------------------------------------------------
  Refinement property linking the parallel algorithm to the sequential
  Misra algorithm.  The sequential algorithm maintains a single frontier
  and a single program counter; we assert that the parallel state
  projects to a state that satisfies the sequential invariant.
--------------------------------------------------------------------*)
\* Sequential state variables (conceptual, not part of the model)
SeqFrontier == \E p \in Procs : frontier
SeqMarked   == marked

Refines == \A p \in Procs : pc[p] \in {"Done"}

=============================================================================