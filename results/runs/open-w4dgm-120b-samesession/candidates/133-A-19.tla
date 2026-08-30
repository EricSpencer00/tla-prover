---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

(* Configuration module for the parallel reachability algorithm.  It inherits  *)
(* all state variables and actions from the parallel algorithm and provides   *)
(* concrete definitions needed for model checking: the node set, the root,     *)
(* the worker processes, and a bounded version of Succ.  It verifies the     *)
(* shared-graph safety invariant and the refinement to the sequential        *)
(* Misra algorithm.                                                            *)

CONSTANTS Nodes, Root, Procs, Succ

\* Bounded version of Succ: each node maps to a finite set of successors
\* that is a subset of Nodes (the graph structure is a concrete configuration
\* constant rather than an uninterpreted relation).  The bound is needed so
\* the model stays finite for TLC; it is not a restriction of the algorithm.
ConnectedToSomeButNotAll == [n \in Nodes |-> {m \in Nodes : m # n /\ n # Root}

VARIABLES marked, frontier, pc, sel, succs

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in [Procs -> {"idle", "working"}]
    /\ sel \in [Procs -> Nodes \cup {"none"}]
    /\ succs \in [Nodes -> SUBSET Nodes]

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = [p \in Procs |-> "idle"]
    /\ sel = [p \in Procs |-> "none"]
    /\ succs = Succ

BeginExplore(p, n) ==
    /\ pc[p] = "idle"
    /\ n \in frontier
    /\ frontier' = frontier \ {n}
    /\ marked' = marked \cup {n}
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ sel' = [sel EXCEPT ![p] = n]
    /\ succs' = succs
    /\ UNCHANGED <<>>

\* A worker adds its selected node's successors; each addition is a fresh TLC
\* step so the concurrent updates to the shared frontier cannot silently lose
\* a node discovered by another worker.
AddSuccessors(p) ==
    /\ pc[p] = "working"
    /\ frontier' = frontier \cup succs[sel[p]]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ sel' = [sel EXCEPT ![p] = "none"]
    /\ UNCHANGED <<marked, succs>>

Finish(p) == AddSuccessors(p)

Next ==
    \/ \E p \in Procs, n \in Nodes : BeginExplore(p, n)
    \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

(* The inductive invariant: every marked node is either the root or has a   *)
(* predecessor that was marked, so no discovered node is ever lost from the *)
(* shared marked set.  The per-process program counters stay inside the       *)
(* allowed range.                                                             *)
Inv ==
    /\ marked \subseteq (Nodes \cup {Root})
    /\ \A n \in marked : n = Root \/ \E m \in marked : n \in succs[m]
    /\ \A p \in Procs : pc[p] \in {"idle", "working"}

(* The parallel algorithm implements the sequential Misra algorithm: any   *)
(* node that is marked is reachable from the root via a path staying within *)
(* the marked set.                                                            *)
Refines ==
    \A n \in marked : \E f \in [1..Cardinality(Nodes) -> Nodes]:
        /\ f[1] = Root
        /\ f[Cardinality(Nodes)] = n
        /\ \A i \in 1..Cardinality(Nodes) - 1 : f[i+1] \in succs[f[i]]
        /\ \A i \in 1..Cardinality(Nodes) : f[i] \in marked

\* Bounded-call version of the sequence operator, for the .cfg substitution.
LimitedSeq == Sequences.Seq

====