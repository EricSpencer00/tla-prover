---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, SeqReachabilityAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

(* ---------------------------------------------------------------------- *)
(* State variables *)
VARIABLES marked, frontier, pc

(* ---------------------------------------------------------------------- *)
(* Helper definitions (may be provided by extended modules) *)
(* Succ[n] : the set of successors of node n *)
(* Reachable(S) : the set of nodes reachable from a set S *)

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

(* ---------------------------------------------------------------------- *)
(* Next-state relation (algorithmic steps) *)
Next ==
    \/ (* take a node from the frontier, mark it and add its successors *)
        \E n \in frontier :
            /\ marked' = marked \cup {n}
            /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ (marked \cup frontier))
            /\ pc' = pc
    \/ (* no nodes left in frontier – stay in a terminal state *)
        /\ frontier = {}
        /\ marked' = marked
        /\ frontier' = frontier
        /\ pc' = pc

vars == <<marked, frontier, pc>>

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Invariant 1: type correctness and successor condition *)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

(* ---------------------------------------------------------------------- *)
(* Invariant 2: reachability equivalence using Lemma 1 *)
Inv2 ==
    (marked \cup Reachable(frontier)) = Reachable(marked \cup frontier)

(* ---------------------------------------------------------------------- *)
(* Invariant 3: reachability from the root using Lemma 2 and Lemma 3 *)
Inv3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == <<Inv1, Inv2, Inv3>>

(* ---------------------------------------------------------------------- *)
(* Termination predicate *)
Terminated == frontier = {}

(* ---------------------------------------------------------------------- *)
(* Partial correctness theorem (property) *)
Correctness ==
    Terminated => marked = Reachable({Root})

PROPERTIES == <<Correctness>>

=============================================================================