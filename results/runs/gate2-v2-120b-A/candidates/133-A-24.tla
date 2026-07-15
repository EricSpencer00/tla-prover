---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, sel, succ

(*********************************************************************
 * Derived constants
 *********************************************************************)
NodeSeq == Seq

(*********************************************************************
 * State variable definitions
 *********************************************************************)
(* The set of nodes that have been discovered *)
marked \in SUBSET Nodes

(* The current frontier of nodes to be explored *)
frontier \in SUBSET Nodes

(* Program counter for each process, ranges over a small set of labels *)
pc \in [Procs -> {"Idle", "Select", "Explore", "Done"}]

(* The node currently selected by each process, or the special value "None" *)
sel \in [Procs -> (Nodes \cup {"None"})]

(* The set of successors that each process has computed for its selected node *)
succ \in [Procs -> SUBSET Nodes]

(*********************************************************************
 * Helper definitions
 *********************************************************************)
IsIdle(p) == pc[p] = "Idle"
IsDone(p) == pc[p] = "Done"

(*********************************************************************
 * Initial state
 *********************************************************************)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "Idle"]
    /\ sel = [p \in Procs |-> "None"]
    /\ succ = [p \in Procs |-> {}]

(*********************************************************************
 * Actions
 *********************************************************************)

Select(p) ==
    /\ pc[p] = "Idle"
    /\ frontier # {}
    /\ \E n \in frontier :
         /\ sel' = [sel EXCEPT ![p] = n]
         /\ frontier' = frontier \ {n}
    /\ pc' = [pc EXCEPT ![p] = "Explore"]
    /\ UNCHANGED <<marked, succ>>

Explore(p) ==
    /\ pc[p] = "Explore"
    /\ sel[p] \in Nodes
    /\ succ' = [succ EXCEPT ![p] = Succ[sel[p]]]
    /\ marked' = marked \cup succ[p] \cup {sel[p]}
    /\ frontier' = frontier \cup succ[p]
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ sel' = [sel EXCEPT ![p] = "None"]
    /\ UNCHANGED <<succ>>

Reset(p) ==
    /\ pc[p] = "Done"
    /\ pc' = [pc EXCEPT ![p] = "Idle"]
    /\ UNCHANGED <<marked, frontier, sel, succ>>

Next ==
    \/ \E p \in Procs : Select(p)
    \/ \E p \in Procs : Explore(p)
    \/ \E p \in Procs : Reset(p)

(*********************************************************************
 * Specification
 *********************************************************************)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succ>>

(*********************************************************************
 * Invariant (type correctness + basic control‑flow)
 *********************************************************************)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"Idle", "Select", "Explore", "Done"}]
    /\ sel \in [Procs -> (Nodes \cup {"None"})]
    /\ succ \in [Procs -> SUBSET Nodes]
    /\ \A p \in Procs :
         (pc[p] = "Idle" => sel[p] = "None")
         /\ (pc[p] = "Select" => sel[p] = "None")
         /\ (pc[p] = "Explore" => sel[p] \in Nodes)
         /\ (pc[p] = "Done" => sel[p] = "None")

(*********************************************************************
 * Refinement property (placeholder for the Misra algorithm invariant)
 *********************************************************************)
Refines == Inv

====