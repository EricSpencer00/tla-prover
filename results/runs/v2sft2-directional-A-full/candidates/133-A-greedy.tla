---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, selected, succSet

(* ----------------------------------------------------------------------
   Derived constants
   ---------------------------------------------------------------------- *)
NodesSet == Nodes
RootNode == Root
ProcSet == Procs
SuccFunc == Succ
SeqBound == Seq

(* ----------------------------------------------------------------------
   Type correctness invariant (used by the sequential module)
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \subseteq NodesSet
    /\ frontier \subseteq NodesSet
    /\ pc \in [ProcSet -> {"Init", "Select", "Add", "Done"}]
    /\ selected \in [ProcSet -> NodesSet]
    /\ succSet \in [ProcSet -> [NodesSet -> BOOLEAN]]
    /\ \A p \in ProcSet : \A n \in NodesSet : succSet[p][n] => n \in SuccFunc[n]

(* ----------------------------------------------------------------------
   Control-flow invariant (used by the parallel module)
   ---------------------------------------------------------------------- *)
ControlFlow ==
    /\ pc[1] = "Init"
    /\ frontier = {RootNode}
    /\ marked = {}

(* ----------------------------------------------------------------------
   Initial state (identical to the parallel algorithm's Init)
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked = {}
    /\ frontier = {RootNode}
    /\ pc = [p \in ProcSet |-> "Init"]
    /\ selected = [p \in ProcSet |-> RootNode]
    /\ succSet = [p \in ProcSet |-> [n \in NodesSet |-> FALSE]]

(* ----------------------------------------------------------------------
   Actions for each worker process
   ---------------------------------------------------------------------- *)
Select(p) ==
    /\ pc[p] = "Init"
    /\ pc' = [pc EXCEPT ![p] = "Select"]
    /\ selected' = [selected EXCEPT ![p] = CHOOSE n \in frontier : TRUE]
    /\ UNCHANGED <<marked, frontier, succSet>>

Add(p) ==
    /\ pc[p] = "Select"
    /\ n = selected[p]
    /\ pc' = [pc EXCEPT ![p] = "Add"]
    /\ marked' = marked \cup {n}
    /\ frontier' = (frontier \ {n}) \cup SuccFunc[n]
    /\ succSet' = [succSet EXCEPT ![p][n] = TRUE]
    /\ UNCHANGED <<pc, selected>>

Done(p) ==
    /\ pc[p] = "Add"
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<marked, frontier, selected, succSet>>

(* ----------------------------------------------------------------------
   Next-state relation (any enabled worker may take its step)
   ---------------------------------------------------------------------- *)
Next ==
    \E p \in ProcSet :
        \/ Select(p)
        \/ Add(p)
        \/ Done(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succSet>>

(* ----------------------------------------------------------------------
   Safety invariant (type correctness + control flow)
   ---------------------------------------------------------------------- *)
Inv == TypeOK /\ ControlFlow

(* ----------------------------------------------------------------------
   Refinement property: the parallel algorithm implements the sequential Misra algorithm
   (placeholder for the actual refinement relation)
   ---------------------------------------------------------------------- *)
Refines ==
    \A p \in ProcSet : pc[p] = "Done"

====