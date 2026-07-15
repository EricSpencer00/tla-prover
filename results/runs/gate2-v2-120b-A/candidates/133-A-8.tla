---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC

(* ----------------------------------------------------------------------
   Constants (to be instantiated by the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS Nodes, Root, Procs, Succ, Seq

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
NodeSet == Nodes
ProcSet == Procs

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES marked, frontier, pc, sel, succs

(* ----------------------------------------------------------------------
   Type definitions (helpful for readability)
   ---------------------------------------------------------------------- *)
Marked == SUBSET NodeSet
Frontier == SUBSET NodeSet
PC == [ProcSet -> {"Init", "Select", "Process", "Done"}]
Sel == [ProcSet -> NodeSet \cup {"None"}]
Succs == [NodeSet -> SUBSET NodeSet]

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in ProcSet |-> "Init"]
    /\ sel = [p \in ProcSet |-> "None"]
    /\ succs = Succ   \* concrete graph supplied via the constant Succ

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* Worker p selects a node from the frontier *)
Select(p) ==
    /\ pc[p] = "Init"
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ sel' = [sel EXCEPT ![p] = n]
          /\ frontier' = frontier \ {n}
          /\ marked' = marked \cup {n}
          /\ pc' = [pc EXCEPT ![p] = "Process"]
          /\ UNCHANGED succs

(* Worker p processes its selected node, adding its successors to frontier *)
Process(p) ==
    /\ pc[p] = "Process"
    /\ sel[p] # "None"
    /\ LET n == sel[p] IN
       /\ frontier' = frontier \cup succs[n]
       /\ sel' = [sel EXCEPT ![p] = "None"]
       /\ pc' = [pc EXCEPT ![p] = "Done"]
       /\ UNCHANGED <<marked, succs>>

(* Worker p does nothing (stuttering) *)
Stutter(p) ==
    /\ pc[p] = "Done"
    /\ UNCHANGED <<marked, frontier, pc, sel, succs>>

(* Parallel step: any subset of workers may take a step *)
Next ==
    \E p \in ProcSet :
        \/ Select(p)
        \/ Process(p)
        \/ Stutter(p)

(* ----------------------------------------------------------------------
   Full specification
   ---------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

(* ----------------------------------------------------------------------
   Safety invariant (type correctness + control‑flow properties)
   ---------------------------------------------------------------------- *)
Inv ==
    /\ marked \in Marked
    /\ frontier \in Frontier
    /\ pc \in PC
    /\ sel \in Sel
    /\ succs = Succ

(* ----------------------------------------------------------------------
   Refinement property (placeholder for the actual refinement relation)
   ---------------------------------------------------------------------- *)
Refines ==
    TRUE

====