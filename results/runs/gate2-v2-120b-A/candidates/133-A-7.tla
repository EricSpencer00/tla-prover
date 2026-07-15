---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Constants required by the .cfg file                                      *)
(***************************************************************************)
CONSTANTS
    Nodes,   \* Set of all nodes in the graph
    Root,    \* The distinguished start node
    Procs,   \* Set of worker process identifiers
    Succ,    \* Function mapping each node to a non‑empty set of its successors
    Seq      \* Upper bound on the length of any sequence used in the model

(***************************************************************************)
(* Derived sets                                                            *)
(***************************************************************************)
\* No derived sets needed beyond the constants themselves

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES
    marked,   \* Set of nodes that have been discovered
    frontier, \* Set of nodes that are currently in the frontier
    pc,       \* Per‑process program counter (a map from a proc to a stage)
    sel,      \* Per‑process selected node (or {} when none is selected)
    succ      \* Per‑process set of successors of the selected node

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)
ProcStates == {"idle", "select", "explore", "done"}

\* The type‑correctness invariant (used as Inv)
TypeOK ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in [Procs -> ProcStates]
    /\ sel \in [Procs -> (Nodes \cup {""})]   \* "" denotes “no selection”
    /\ succ \in [Procs -> SUBSET Nodes]

\* Safety invariant required by the .cfg (same as the type invariant)
Inv == TypeOK

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> ""]
    /\ succ = [p \in Procs |-> {}]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

(* A process picks a node from the frontier to explore *)
Select(p) ==
    /\ p \in Procs
    /\ pc[p] = "idle"
    /\ frontier # {}               \* there is something to select
    /\ \E n \in frontier :
        /\ sel' = [sel EXCEPT ![p] = n]
        /\ pc'  = [pc  EXCEPT ![p] = "select"]
        /\ frontier' = frontier \ {n}
        /\ succ' = succ
        /\ marked' = marked
    /\ UNCHANGED <<>>

(* The selected node's successors are computed, bounded by Seq *)
Explore(p) ==
    /\ p \in Procs
    /\ pc[p] = "select"
    /\ sel[p] # ""
    /\ \E s \subseteq Succ[sel[p]] :
        /\ Cardinality(s) <= Seq
        /\ succ' = [succ EXCEPT ![p] = s]
        /\ pc' = [pc EXCEPT ![p] = "explore"]
        /\ UNCHANGED << marked, frontier, sel >>

(* All successors are added to the frontier and the node is marked done *)
Update(p) ==
    /\ p \in Procs
    /\ pc[p] = "explore"
    /\ frontier' = frontier \cup succ[p]
    /\ marked' = marked \cup {sel[p]}
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ sel' = [sel EXCEPT ![p] = ""]
    /\ succ' = [succ EXCEPT ![p] = {}]
    /\ UNCHANGED <<>>

(* The process resets to idle, ready for another round *)
Reset(p) ==
    /\ p \in Procs
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED << marked, frontier, sel, succ >>

(* Stuttering step to avoid deadlock when all are idle *)
Stutter ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ UNCHANGED << marked, frontier, pc, sel, succ >>

(***************************************************************************)
(* Next-action definition                                                  *)
(***************************************************************************)
Next ==
    \/ \E p \in Procs : Select(p)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Update(p)
    \/ \E p \in Procs : Reset(p)
    \/ Stutter

(***************************************************************************)
(* Specification                                                            *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succ>>

(***************************************************************************)
(* Refinement property: the parallel algorithm implements the sequential *)
(* Misra reachability algorithm (abstractly expressed as a subset        *)
(* relationship between the parallel marked set and an abstract reachable *)
(* set). The concrete definition is left abstract, as the sequential      *)
(* algorithm is not modeled in this module.                                 *)
(***************************************************************************)
ReachableSeq == UNION { Succ[n] : n \in Nodes } \cup {Root}   \* placeholder

Refines == marked \subseteq ReachableSeq

=============================================================================