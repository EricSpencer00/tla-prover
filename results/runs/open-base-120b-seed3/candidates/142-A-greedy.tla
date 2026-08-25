---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init == SeqReachAlg!Init

Next == SeqReachAlg!Next

(* Invariant 1: type correctness and successor condition *)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
        \A s \in Succ[n] : s \in marked \/ s \in frontier

(* Invariant 2: marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier) *)
Inv2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

(* Invariant 3: Reachable({Root}) = marked ∪ Reachable(frontier) *)
Inv3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

Invariants == Inv1 /\ Inv2 /\ Inv3

Properties == Invariants

Spec == Init /\ [][Next]_vars

====