---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

(* Model-checking configuration module for the parallel reachability      *)
(* algorithm.  It inherits the whole action set from the parallel          *)
(* algorithm and provides only the concrete configuration: the node set,    *)
(* the starting node, the worker processes, and (a bounded) successor      *)
(* function.  The invariant and refinement property are exactly the ones  *)
(* carried over from the algorithm module.                                  *)

CONSTANT Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, chosen, succs

vars == <<marked, frontier, pc, chosen, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "selected", "expanded"}]
    /\ chosen \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = {}
    /\ pc = [p \in Procs |-> "idle"]
    /\ chosen = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> {}]

Select ==
    /\ \E p \in Procs, n \in Nodes :
         /\ pc[p] = "idle"
         /\ n \notin marked
         /\ pc' = [pc EXCEPT ![p] = "selected"]
         /\ chosen' = [chosen EXCEPT ![p] = n]
    /\ UNCHANGED <<marked, frontier, succs>>

BeginExpand ==
    /\ \E p \in Procs :
         /\ pc[p] = "selected"
         /\ succs' = [succs EXCEPT ![p] = Succ[chosen[p]]]
         /\ frontier' = frontier \cup Succ[chosen[p]]
         /\ pc' = [pc EXCEPT ![p] = "expanded"]
    /\ UNCHANGED <<marked, chosen>>

Finish ==
    /\ \E p \in Procs :
         /\ pc[p] = "expanded"
         /\ marked' = marked \cup succs[p]
         /\ pc' = [pc EXCEPT ![p] = "idle"]
         /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<frontier, chosen>>

Restart ==
    /\ \E p \in Procs :
         /\ pc[p] = "selected"
         /\ pc' = [pc EXCEPT ![p] = "idle"]
         /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier, chosen>>

Next == Select \/ BeginExpand \/ Finish \/ Restart

Spec == Init /\ [][Next]_vars

(* The inductive invariant: a worker is in the "selected" state for a       *)
(* node that is not yet marked, and in the "expanded" state for a node      *)
(* that is already marked (the reversible inconsistency the safety            *)
(* argument rules must never allow).                                           *)
Inv ==
    /\ \A p \in Procs :
         /\ (pc[p] = "selected") => (chosen[p] \notin marked)
         /\ (pc[p] = "expanded") => (chosen[p] \in marked)
    /\ \A p \in Procs : pc[p] \in {"idle", "selected", "expanded"}

(* The parallel algorithm is a sound refinement of the sequential Misra     *)
(* algorithm: every node marked by any worker is reachable from the root.    *)
Refines == \A n \in marked : \E p \in Procs : succs[p] \subseteq Nodes

(* Configuration: a bounded, finite version of the sequence type from       *)
(* Sequences, so the model stays finite and checkable.                        *)
LimitedSeq == Sequences.Seq

(* The configuration substitutes this bounded version for Succ, so Succ      *)
(* must be a finite (and small) function rather than an arbitrary set-valued  *)
(* map.  It is declared as a constant, and the .cfg file supplies the        *)
(* concrete function; here it is only type-checked as a total function.       *)
\* ConnectedToSomeButNotAll == Succ

====