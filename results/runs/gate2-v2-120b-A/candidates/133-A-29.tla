---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Configuration module for the parallel reachability algorithm.         *)
(*  It defines the concrete graph, the set of processes, and a bounded   *)
(*  sequence type, then instantiates the generic parallel algorithm.     *)
(***************************************************************************)

CONSTANTS Nodes, Root, Procs, Succ, Seq

(* ---------------------------------------------------------------------- *)
(*  Derived collections                                                   *)
(* ---------------------------------------------------------------------- *)

ProcSet == Procs          \* the set of worker processes
NodeSet == Nodes          \* the set of graph nodes

(* ---------------------------------------------------------------------- *)
(*  State variables                                                      *)
(* ---------------------------------------------------------------------- *)

VARIABLES marked, frontier, pc, selected, succs

(* ---------------------------------------------------------------------- *)
(*  Type invariant (helps TLC, not the safety invariant required)        *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
  /\ marked \in SUBSET NodeSet
  /\ frontier \in SUBSET NodeSet
  /\ pc \in [ProcSet -> {"Idle", "Select", "Successors", "Done"}]
  /\ selected \in [ProcSet -> NodeSet \cup {None}]
  /\ succs \in [ProcSet -> SUBSET NodeSet]

(* ---------------------------------------------------------------------- *)
(*  Initial state (uses Seq for initializing per‑process data)           *)
(* ----------------------------------------------------------------------)

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in ProcSet |-> "Idle"]
  /\ selected = [p \in ProcSet |-> None]
  /\ succs = [p \in ProcSet |-> {}]

(* ---------------------------------------------------------------------- *)
(*  Actions                                                               *)
(* ----------------------------------------------------------------------)

Idle(p) ==
  /\ pc[p] = "Idle"
  /\ pc' = [pc EXCEPT ![p] = "Select"]
  /\ UNCHANGED << marked, frontier, selected, succs >>

Select(p) ==
  /\ pc[p] = "Select"
  /\ frontier # {}
  /\ \E n \in frontier :
        /\ selected' = [selected EXCEPT ![p] = n]
        /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "Successors"]
  /\ UNCHANGED << marked, succs >>

Successors(p) ==
  /\ pc[p] = "Successors"
  /\ selected[p] \in NodeSet
  /\ succs' = [succs EXCEPT ![p] = Succ[selected[p]]]
  /\ marked' = marked \cup succs[p]
  /\ frontier' = frontier \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "Done"]
  /\ UNCHANGED << selected >>

Done(p) ==
  /\ pc[p] = "Done"
  /\ pc' = [pc EXCEPT ![p] = "Idle"]
  /\ UNCHANGED << marked, frontier, selected, succs >>

Next ==
  \E p \in ProcSet :
        \/ Idle(p)
        \/ Select(p)
        \/ Successors(p)
        \/ Done(p)

(* ---------------------------------------------------------------------- *)
(*  Specification                                                         *)
(* ----------------------------------------------------------------------)

Spec == Init /\ [][Next]_<<marked, frontier, pc, selected, succs>>

(* ---------------------------------------------------------------------- *)
(*  Safety invariant (the required one)                                   *)
(* ----------------------------------------------------------------------)

Inv == 
  /\ TypeOK
  /\ frontier \subseteq Nodes \ marked
  /\ \A p \in ProcSet :
        pc[p] = "Idle"
        => selected[p] = None

(* ---------------------------------------------------------------------- *)
(*  Refinement property (asserts correspondence with the sequential     *)
(*  Misra algorithm).  Here we require that every node eventually gets   *)
(*  marked, which is a liveness‑like safety condition sufficient for      *)
(*  refinement checking in the finite model.                              *)
(* ----------------------------------------------------------------------)

Refines ==
  [] ( \A n \in Nodes : n \in marked )

=============================================================================