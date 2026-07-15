---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the .cfg file.
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root, Procs, Succ, Seq

(*-----------------------------------------------------------------
  State variables (inherited from the parallel algorithm).
-----------------------------------------------------------------*)
VARIABLES
    marked,          \* Set of nodes that have been marked as reachable
    frontier,       \* Set of nodes currently in the frontier
    pc,             \* Mapping from each process to its program counter
    sel,            \* Mapping from each process to its currently selected node
    succSet         \* Mapping from each process to the set of successors of its selected node

(*-----------------------------------------------------------------
  Helper definitions.
-----------------------------------------------------------------*)
ProcIDs == Procs

PCVals == {"idle", "select", "expand", "done"}

InitState ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in ProcIDs |-> "idle"]
    /\ sel = [p \in ProcIDs |-> NULL]
    /\ succSet = [p \in ProcIDs |-> {}]

(*-----------------------------------------------------------------
  Actions (the parallel reachability algorithm, unmodified).
-----------------------------------------------------------------*)

Select ==
    /\ \E p \in ProcIDs :
        /\ pc[p] = "idle"
        /\ frontier # {}
        /\ sel' = [sel EXCEPT ![p] = CHOOSE n \in frontier : TRUE]
        /\ pc'  = [pc  EXCEPT ![p] = "expand"]
        /\ UNCHANGED <<marked, frontier, succSet>>

Expand ==
    /\ \E p \in ProcIDs :
        /\ pc[p] = "expand"
        /\ succSet' = [succSet EXCEPT ![p] = Succ[sel[p]]]
        /\ marked'   = marked \cup succSet[p]
        /\ frontier' = (frontier \ {sel[p]}) \cup succSet[p]
        /\ pc'       = [pc EXCEPT ![p] = "idle"]
        /\ sel'      = [sel EXCEPT ![p] = NULL]
        /\ UNCHANGED <<succSet>>

Done ==
    /\ \A p \in ProcIDs : pc[p] = "done"
    /\ UNCHANGED <<marked, frontier, pc, sel, succSet>>

(*-----------------------------------------------------------------
  Next-state relation.
-----------------------------------------------------------------*)
Next == \/ Select
        \/ Expand
        \/ Done

(*-----------------------------------------------------------------
  Specification.
-----------------------------------------------------------------*)
Spec == InitState /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(*-----------------------------------------------------------------
  Safety invariant (Inductive invariant from the parallel algorithm).
-----------------------------------------------------------------*)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ frontier = {} => marked = Nodes
    /\ \A p \in ProcIDs :
          /\ pc[p] \in PCVals
          /\ (pc[p] = "idle" => sel[p] = NULL)
          /\ (pc[p] = "expand" => sel[p] \in frontier)
          /\ (pc[p] = "idle" => succSet[p] = {})
          /\ (pc[p] = "expand" => succSet[p] = Succ[sel[p]])

(*-----------------------------------------------------------------
  Refinement property: the parallel algorithm implements the sequential
  Misra algorithm (abstractly, marked set equals the set obtained by the
  sequential algorithm on the same graph).
-----------------------------------------------------------------*)
(* A simple formulation that the set of marked nodes is exactly the set
   of nodes reachable from the root in the underlying graph. *)
ReachableFromRoot ==
    LET R == RECURSIVE R(_)
        R(n) == n = Root \/ \E m \in Nodes : n \in Succ[m] /\ R(m)
    IN { n \in Nodes : R(n) }

Refines == marked = ReachableFromRoot

====