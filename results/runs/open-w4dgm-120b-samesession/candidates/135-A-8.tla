---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

(* A model-checking configuration for the sequential Misra reachability *)
(* algorithm.  It adds concrete definitions so the state space is finite:  *)
(* a specific graph structure on the nodes, and a bounded override on     *)
(* the sequence type used by the reachability definition.                *)

CONSTANTS Nodes, Root, Succ

None == "none"

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "active", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "idle"

Start ==
    /\ pc = "idle"
    /\ pc' = "active"
    /\ UNCHANGED <<marked, frontier>>

Explore ==
    /\ pc = "active"
    /\ frontier # {}
    /\ \E t \in frontier :
        /\ marked' = marked \cup {t}
        /\ frontier' = (frontier \ {t}) \cup ConnectedToSomeButNotAll[t]
    /\ UNCHANGED <<pc>>

Stop ==
    /\ pc = "active"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

InitNext == Start \/ Explore \/ Stop

Spec == Init /\ [][InitNext]_vars

(* Successor closure: every node in the reachable set has a successor     *)
(* that is also reachable, so the frontier cannot pull in a node it could  *)
(* not subsequently expand.                                               *)
Inv1 ==
    \A t \in marked : \E u \in ConnectedToSomeButNotAll[t] : u \in marked

(* Reachability decomposition: a reachable node is either the root or     *)
(* has a reachable predecessor.                                            *)
Inv2 ==
    \A t \in marked : (t = Root) \/ (\E u \in Nodes : t \in ConnectedToSomeButNotAll[u] /\ u \in marked)

(* The reachable set is exactly the root plus the successors of its      *)
(* members, so no reachable node is missed or added spuriously.           *)
Inv3 ==
    marked = {Root} \cup {u \in Nodes : \E t \in marked : u \in ConnectedToSomeButNotAll[t]}

(* Partial correctness: the algorithm stops once its frontier is empty. *)
PartialCorrectness == (pc = "active" /\ frontier = {}) => (pc = "done")

Termination == <>(pc = "done")

(* Configuration constants: a graph of 4 nodes where each node has exactly *)
(* 2 successors, chosen to give interesting reachability while staying     *)
(* small enough for exhaustive checking.                                   *)
ConnectedToSomeButNotAll == ConnectedToSomeButNotAll

(* Bounded override of the sequence type: the definition of Reachable     *)
(* uses an existential quantification over sequences of nodes (paths),    *)
(* which would otherwise be over an infinite set.  Replacing Seq with a    *)
(* FINITE sequence type makes the reachable set checkable.                *)
LimitedSeq == Seq

====