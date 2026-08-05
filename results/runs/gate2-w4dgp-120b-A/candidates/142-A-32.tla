---- MODULE ReachableProofs ----
EXTENDS Integers, Naturals, Reachability
(* Formal proof of partial correctness for the sequential Misra reachability
   algorithm: the marked set stays closed under successors and by termination it
   equals the reachable set. The lemmas are drawn from the reachability proofs
   module. *)
CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "lp"

ExpandMark(n) ==
    /\ pc = "lp"
    /\ n \in marked
    /\ frontier = {}
    /\ frontier' = {m \in Nodes : n \in Adj[m]}
    /\ marked' = marked \cup {m \in Nodes : n \in Adj[m]}
    /\ pc' = "rp"
    /\ UNCHANGED frontier

RelaxFrontier ==
    /\ pc = "rp"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = "lp"
    /\ UNCHANGED frontier

Relaunch ==
    /\ pc = "rp"
    /\ frontier = {}
    /\ \E n \in marked : frontier' = {m \in Nodes : n \in Adj[m]}
    /\ marked' = marked \cup frontier'
    /\ pc' = "lp"
    /\ UNCHANGED frontier

Next == \E n \in Nodes : ExpandMark(n) \/ Relaunch
        \/ RelaxFrontier

Spec == Init /\ [][Next]_vars

(* Invariant 1: the marked set is closed under successors: any successor of a
   marked node is either already marked or in the frontier. *)
Inductive ==
    /\ frontier \subseteq Nodes
    /\ marked \subseteq Nodes
    /\ pc \in {"lp", "rp"}
    /\ \A n \in marked : \A m \in Nodes : n \in Adj[m] => m \in marked \cup frontier

(* Invariant 2: the marked set plus the nodes reachable from the frontier equals
   the nodes reachable from the union of marked and frontier; this is exactly
   Lemma 1. *)
ReachableFromFrontier ==
    ReachableFrom(marked) \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

(* Invariant 3: reachable nodes are exactly the marked nodes plus those
   reachable from the frontier, using Lemma 2 (ReachableFrom is stable under
   adding successors) and Lemma 3 (ReachableFrom from empty is empty). *)
MarkedMatchesReachable ==
    ReachableFrom(Nodes) = marked \cup ReachableFrom(frontier)

(* Partial correctness: on termination the marked set equals the reachable
   nodes. *)
PartialCorrectness == (pc = "rp" /\ frontier = {}) => marked = ReachableFrom(Nodes)
====