---- MODULE Reachable ----
EXTENDS Naturals, Sequences

(* A specification of Misra's algorithm for computing the reachable nodes from a *)
(* root in a directed graph.  The algorithm is a variant of breadth-first search   *)
(* in which the visited (marked) set and the frontier set may overlap, which is    *)
(* what makes it amenable to parallel implementation.  The invariant chain below   *)
(* captures partial correctness: the marked set is exactly the reachable set.     *)

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* The main action, with nondeterministic choice of a frontier node.  The
\* overlap is allowed: a node may stay in frontier after being marked.
Explore(n) ==
    /\ pc = "running"
    /\ n \in frontier
    /\ \/ (n \notin marked /\ marked' = marked \cup {n}
                           /\ frontier' = frontier \cup Succ[n])
       \/ (n \in marked /\ frontier' = frontier \ {n})
    /\ UNCHANGED pc

Terminate ==
    /\ pc = "running"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED << marked, frontier >>

Next == \E n \in Nodes : Explore(n) \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ \A n \in Nodes : WF_vars(Explore(n))

(* Every successor of a marked node is accounted for: already marked or waiting. *)
Inv1 ==
    \A n \in Nodes : (n \in marked) => (Succ[n] \subseteq (marked \cup frontier))

(* The reachable set from the union is exactly the union of the two reachable   *)
(* pieces: the marked set, and the frontier's contribution.                     *)
Inv2 ==
    \A S \in SUBSET Nodes :
        (ReachableFrom(S) = S \cup ReachableFrom(frontier)
            => ReachableFrom(S) = S \cup ReachableFrom(frontier))

(* The marked set plus the frontier's reachable set is the full reachable set.  *)
Inv3 ==
    ReachableFrom({Root}) = (marked \cup ReachableFrom(frontier))

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

(* Under weak fairness of the frontier-choosing action, a finite reachable set  *)
(* must collapse to the empty frontier, i.e. the algorithm terminates.         *)
Termination == (Marked \cup Frontier) # {} ~> Frontier = {}
====