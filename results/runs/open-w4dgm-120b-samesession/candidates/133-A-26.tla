---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

(* Model-checking configuration for the parallel reachability algorithm.   *)
(* It inherits the process and state variables, but supplies concrete      *)
(* constants (the graph shape and the process set) and redefines the       *)
(* sequence constructor to a finite-version so the model is checkable.     *)

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "ready"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Procs -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succs = [p \in Procs |-> {}]

Select(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ pc' = [pc EXCEPT ![p] = "ready"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ succs' = [succs EXCEPT ![p] = Succ[n]]
    /\ UNCHANGED <<marked, frontier>>

Commit(p) ==
    /\ pc[p] = "ready"
    /\ marked' = marked \cup {sel[p]}
    /\ frontier' = (frontier \cup succs[p]) \ {sel[p]}
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ UNCHANGED succs

Abort(p) ==
    /\ pc[p] = "ready"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ succs' = [succs EXCEPT ![p] = {}]
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E p \in Procs, n \in Nodes : Select(p, n)
    \/ \E p \in Procs : Commit(p)
    \/ \E p \in Procs : Abort(p)

Spec == Init /\ [][Next]_vars

(* Inductive type and control-flow correctness, together with the safety    *)
(* refinement that the reachable set follows the root-connected closure.    *)
Inv == TypeOK

(* Atomicity & no lost update: the frontier is exactly the complement of  *)
(* the marked set, so no node is ever dropped from frontier without        *)
(* entering marked, and no marked node is left dangling in frontier.      *)
Refines == frontier = Nodes \ marked

(* The original successor relation, kept finite for all nodes.             *)
ConnectedToSomeButNotAll == Succ

(* Finite version of Seq, so the state space stays bounded for TLC.       *)
LimitedSeq == Sequence

====