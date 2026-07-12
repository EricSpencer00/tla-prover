---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Procs, Succ, Seq

(* ----------------------------------------------------------------------
   Variables inherited from the parallel reachability algorithm:
     * marked     : set of nodes that have been discovered
     * frontier   : sequence (queue) of nodes to be processed
     * pc         : mapping from each process to its program counter
     * selected   : mapping from each process to the node it has currently selected
     * succMap    : mapping from each process to the set of successors it has retrieved
   ---------------------------------------------------------------------- *)

VARIABLES marked, frontier, pc, selected, succMap

(* ----------------------------------------------------------------------
   Type definitions (used only for the type correctness part of the invariant)
   ---------------------------------------------------------------------- *)

NodeSet == Nodes
ProcSet == Procs

(* ----------------------------------------------------------------------
   Initial state (inherited from the sequential algorithm's configuration)
   ---------------------------------------------------------------------- *)

Init ==
    /\ marked = {}
    /\ frontier = <<Root>>
    /\ pc = [p \in ProcSet |-> "Init"]
    /\ selected = [p \in ProcSet |-> None]
    /\ succMap = [p \in ProcSet |-> {}]

(* ----------------------------------------------------------------------
   Actions (identical to those in the parallel algorithm; only the shape is defined here)
   ---------------------------------------------------------------------- *)

(* A process with program counter "Select" picks the next node from the frontier *)
Select(p) ==
    /\ pc[p] = "Select"
    /\ frontier # <<>>
    /\ LET v == Head(frontier) IN
       /\ frontier' = Tail(frontier)
       /\ selected[p]' = v
       /\ pc[p]' = "GetSucc"
       /\ UNCHANGED << marked, succMap >>

(* A process with program counter "GetSucc" obtains successors of its selected node *)
GetSucc(p) ==
    /\ pc[p] = "GetSucc"
    /\ selected[p] # None
    /\ succMap[p]' = Succ[selected[p]]
    /\ pc[p]' = "AddToMarked"
    /\ UNCHANGED << marked, frontier, selected >>

(* A process with program counter "AddToMarked" adds successors to marked and frontier *)
AddToMarked(p) ==
    /\ pc[p] = "AddToMarked"
    /\ LET newNodes == succMap[p] \ marked IN
       /\ frontier' = Append(frontier, newNodes)
       /\ marked' = marked \cup succMap[p]
       /\ pc[p]' = "Select"
       /\ selected[p]' = None
       /\ succMap[p]' = {}
    /\ UNCHANGED << succMap >>

(* When no frontier remains, processes stay idle *)
Idle(p) ==
    /\ frontier = <<>>
    /\ pc[p] = "Select"
    /\ UNCHANGED << marked, frontier, pc, selected, succMap >>

(* NEXT relation is the union of all possible actions of all processes *)
Next ==
    \/ \E p \in ProcSet: Select(p)
    \/ \E p \in ProcSet: GetSucc(p)
    \/ \E p \in ProcSet: AddToMarked(p)
    \/ \E p \in ProcSet: Idle(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succMap>>

(* ----------------------------------------------------------------------
   Safety property: type correctness (placeholder for the actual invariant)
   ---------------------------------------------------------------------- *)

Inv ==
    /\ marked \subseteq NodeSet
    /\ frontier \in Seq(NodeSet)
    /\ \A p \in ProcSet: pc[p] \in {"Init", "Select", "GetSucc", "AddToMarked"}
    /\ \A p \in ProcSet: selected[p] = None \/ selected[p] \in NodeSet
    /\ \A p \in ProcSet: succMap[p] \subseteq NodeSet

(* ----------------------------------------------------------------------
   Refinement property: the parallel algorithm implements the sequential Misra algorithm
   ---------------------------------------------------------------------- *)

Refines ==
    (* Placeholder: in a real model the refinement would compare the set of marked nodes
       and the frontier to those produced by the sequential algorithm. *)
    marked = <<>> /\ frontier = <<Root>>

=============================================================================