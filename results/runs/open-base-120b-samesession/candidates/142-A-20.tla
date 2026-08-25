---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

(* ---------- Invariants ---------- *)

(* Invariant 1: type correctness and each successor of a marked node is either marked or in the frontier *)
Inv1 == 
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A n \in Marked :
          \A s \in Succ[n] : s \in Marked \/ s \in Frontier

(* Invariant 2: Marked ∪ Reachable(Frontier) = Reachable(Marked ∪ Frontier) *)
Inv2 == Reachable(Marked) \cup Reachable(Frontier) = Reachable(Marked \cup Frontier)

(* Invariant 3: Reachable({Root}) = Marked ∪ Reachable(Frontier) *)
Inv3 == Reachable({Root}) = Marked \cup Reachable(Frontier)

Invariants == Inv1 /\ Inv2 /\ Inv3

(* ---------- Initialization ---------- *)

Init == 
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "Start"

(* ---------- Actions ---------- *)

Expand ==
    /\ pc = "Start"
    /\ Frontier # {}
    /\ \E n \in Frontier :
          /\ Marked'   = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n}) \cup (Succ[n] \ Marked)
          /\ pc'       = "Start"

Advance ==
    /\ pc = "Start"
    /\ Frontier = {}
    /\ Marked'   = Marked
    /\ Frontier' = Frontier
    /\ pc'       = "Done"

Next == Expand \/ Advance

(* ---------- Specification ---------- *)

Spec == Init /\ [][Next]_(<<Marked, Frontier, pc>>)

(* ---------- Properties ---------- *)

Properties == Invariants

====