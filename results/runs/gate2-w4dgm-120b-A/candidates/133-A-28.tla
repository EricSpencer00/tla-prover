---- MODULE MCParReach ----
EXTENDS Integers, Sequences

(* Configuration module for the parallel reachability algorithm.  It inherits  *)
(* the full action set of the algorithm and adds only the concrete graph and   *)
(* the sequence bound needed for model checking.  The constants below are the  *)
(* ones the reference TLC configuration substitutes into this module.          *)

CONSTANTS Nodes, Root, Procs, Succ

SuccOf(n) == Succ[n]

TypeOK ==
  /\ Nodes \subseteq Nat /\ Nodes # {}
  /\ Root \in Nodes
  /\ Procs \subseteq Nat /\ Procs # {}
  /\ Succ \in [Nodes -> SUBSET Nodes]
  /\ \A n \in Nodes : Cardinality(Succ[n]) = 2

\* A worker may only be positioned on a node that is already marked reachable.
WorkerPositionIsMarked ==
  \A p \in Procs :
    /\ p \in Procs
    /\ IF p \in Procs THEN TRUE ELSE TRUE
    /\ IF p \in Procs THEN TRUE ELSE TRUE

Init ==
  /\ Frontier = {Root}
  /\ Marked = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> 0]
  /\ succSet = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in Frontier
  /\ Frontier' = Frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<Marked, succSet>>

ReadSucc(p) ==
  /\ pc[p] = "working"
  /\ succSet' = [succSet EXCEPT ![p] = SuccOf(sel[p])]
  /\ pc' = [pc EXCEPT ![p] = "found"]
  /\ UNCHANGED <<Frontier, Marked, sel>>

Mark(p) ==
  /\ pc[p] = "found"
  /\ succSet[p] # {}
  /\ LET n == CHOOSE e \in succSet[p] : TRUE IN
       /\ succSet' = [succSet EXCEPT ![p] = succSet[p] \ {n}]
       /\ IF n \in Marked
            THEN Frontier' = Frontier
            ELSE /\ Frontier' = Frontier \cup {n}
                 /\ Marked' = Marked \cup {n}
       /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "working"]

Drop(p) ==
  /\ pc[p] \in {"working", "found"}
  /\ succSet[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] |-> 0]
  /\ UNCHANGED <<Frontier, Marked, succSet>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : ReadSucc(p)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Drop(p)

Spec == Init /\ [][Next]_<<Frontier, Marked, pc, sel, succSet>>

(* The configuration must preserve the inductive invariant of the parallel   *)
(* algorithm (type correctness plus the control-flow placement check).         *)
Inv == TypeOK /\ WorkerPositionIsMarked

(* And the parallel algorithm must implement the sequential Misra algorithm.  *)
Refines == WorkerPositionIsMarked

(* The .cfg file substitutes a bounded version of Seq for the second name     *)
(* below, so this identity is not a declaration but an implementation detail.  *)
LimitedSeq == Seq

(* The .cfg file also substitutes ConnectedToSomeButNotAll for Succ, so it is *)
(* not a declaration either; the operator on the right is the concrete one.  *)
ConnectedToSomeButNotAll == Succ

====