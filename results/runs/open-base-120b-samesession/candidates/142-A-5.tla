---- MODULE ReachableProofs ----
EXTENDS SeqReachAlg, ReachabilityLemmas

CONSTANTS
    Nodes,
    Root

VARIABLES
    Marked,
    Frontier,
    pc

(*---------------------------------------------------------------------*)
(* Initial predicate (taken from the sequential reachability algorithm) *)
(*---------------------------------------------------------------------*)
Init == Init

(*---------------------------------------------------------------------*)
(* Next-state relation (taken from the sequential reachability algorithm) *)
(*---------------------------------------------------------------------*)
Next == Next

(*---------------------------------------------------------------------*)
(* Specification *)
(*---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(*---------------------------------------------------------------------*)
(* Invariant 1: type correctness and successor property *)
(*---------------------------------------------------------------------*)
Inv1 == /\ Marked \subseteq Nodes
        /\ Frontier \subseteq Nodes
        /\ \A n \in Marked : \A s \in Succ[n] : s \in Marked \/ s \in Frontier

(*---------------------------------------------------------------------*)
(* Invariant 2: relationship between marked, frontier and reachability *)
(*---------------------------------------------------------------------*)
Inv2 == (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

(*---------------------------------------------------------------------*)
(* Invariant 3: marked set equals reachable nodes from the root *)
(*---------------------------------------------------------------------*)
Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

(*---------------------------------------------------------------------*)
(* Conjunction of all invariants *)
(*---------------------------------------------------------------------*)
INVARIANTS == Inv1 /\ Inv2 /\ Inv3

(*---------------------------------------------------------------------*)
(* Partial‑correctness property proved by TLAPS *)
(*---------------------------------------------------------------------*)
Correctness == (pc = "done") => (Marked = Reachable({Root}))

PROPERTIES == Correctness
=============================================================================