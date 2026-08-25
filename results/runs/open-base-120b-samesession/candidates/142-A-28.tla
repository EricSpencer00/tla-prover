---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, ReachabilityAlgorithm, ReachabilityLemmas

CONSTANTS Nodes, Root
ASSUME Root \in Nodes

VARIABLES Marked, Frontier, pc

vars == <<Marked, Frontier, pc>>

(* Initial state – a simple placeholder that satisfies the type constraints *)
Init ==
    /\ Marked = {Root}
    /\ Frontier = {}
    /\ pc = "start"

(* Next – a generic stub; the real algorithm actions are defined in the
   extended ReachabilityAlgorithm module. *)
Next ==
    UNCHANGED vars

(* Successor relation – assumed to be provided by ReachabilityAlgorithm *)
Succ(n) == { m \in Nodes : <<n, m>> \in Edge }

(* Invariant 1: type correctness and every successor of a marked node is
   either already marked or in the frontier. *)
Inv1 ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ \A n \in Marked: Succ(n) \subseteq Marked \cup Frontier

(* Invariant 2: marked ∪ reachable(frontier) = reachable(marked ∪ frontier) *)
Inv2 ==
    (Marked \cup Reachable(Frontier)) = Reachable(Marked \cup Frontier)

(* Invariant 3: reachable from the root = marked ∪ reachable(frontier) *)
Inv3 ==
    Reachable({Root}) = Marked \cup Reachable(Frontier)

Invariants == /\ Inv1 /\ Inv2 /\ Inv3

(* Partial‑correctness property: when the algorithm finishes, the marked set
   equals the set of nodes reachable from the root. *)
Properties ==
    (pc = "done") => (Marked = Reachable({Root}))

(* The overall specification *)
Spec == Init /\ [][Next]_vars

====