---- MODULE MCParReach ----
EXTENDS Naturals, TLC

CONSTANTS Nodes, Root, Procs, Succ, Seq

(* ----------------------------------------------------------------------
   Type definitions (helpful for readability, not exported as CONSTANTS)
   ---------------------------------------------------------------------- *)
Node == Nodes
Proc == Procs
NodeSeq == Seq

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES marked, frontier, pc, sel, succSet

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
Marked == marked
Frontier == frontier
PC == pc
Sel == sel
SuccSet == succSet

(* Process identifiers *)
PROCESSES == Proc

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = [p \in PROCESSES |-> "Choose"]
    /\ sel = [p \in PROCESSES |-> {}]
    /\ succSet = [p \in PROCESSES |-> {}]

(* ----------------------------------------------------------------------
   Actions (derived from the description of the parallel algorithm)
   ---------------------------------------------------------------------- *)

Choose(p) ==
    /\ pc[p] = "Choose"
    /\ frontier # {}
    /\ LET v == CHOOSE x \in frontier : TRUE IN
       /\ sel' = [sel EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = "Process"]
       /\ UNCHANGED <<marked, frontier, succSet>>

Process(p) ==
    /\ pc[p] = "Process"
    /\ sel[p] \in frontier
    /\ LET v == sel[p] IN
       /\ marked' = marked \cup {v}
       /\ frontier' = (frontier \ {v}) \cup Succ[v]
       /\ succSet' = [succSet EXCEPT ![p] = Succ[v]]
       /\ pc' = [pc EXCEPT ![p] = "Choose"]
       /\ UNCHANGED <<sel>>

Idle(p) ==
    /\ pc[p] = "Idle"
    /\ UNCHANGED <<marked, frontier, pc, sel, succSet>>

Next ==
    \/ \E p \in PROCESSES : Choose(p)
    \/ \E p \in PROCESSES : Process(p)
    \/ \E p \in PROCESSES : Idle(p)

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(* ----------------------------------------------------------------------
   Invariant (type correctness and control-flow constraints)
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [PROCESSES -> {"Choose", "Process", "Idle"}]
    /\ sel \in [PROCESSES -> Nodes]
    /\ succSet \in [PROCESSES -> SUBSET Nodes]

Inv == TypeOK

(* ----------------------------------------------------------------------
   Refinement property (placeholder for actual relation to sequential spec)
   ---------------------------------------------------------------------- *)
Refines == Inv

====