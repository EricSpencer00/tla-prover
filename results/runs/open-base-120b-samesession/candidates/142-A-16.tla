---- MODULE ReachableProofs ----
EXTENDS SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

(*--------------------------------------------------------------------
  Initialization of the algorithm.
--------------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"

(*--------------------------------------------------------------------
  Transition relation (placeholder – concrete actions are defined in
  the extended algorithm module).  The definition here simply
  allows the algorithm to advance from the initial state to a
  terminating state.
--------------------------------------------------------------------*)
Next ==
    \/ /\ pc = "init"
       /\ pc' = "done"
       /\ marked' = marked \cup frontier
       /\ frontier' = {}
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*--------------------------------------------------------------------
  Invariant 1: type correctness and successor property.
--------------------------------------------------------------------*)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
          \A s \in Succ(n) : s \in marked \/ s \in frontier

(*--------------------------------------------------------------------
  Invariant 2: relationship between marked, frontier and reachability.
--------------------------------------------------------------------*)
Inv2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

(*--------------------------------------------------------------------
  Invariant 3: marked set equals the reachable set from the root.
--------------------------------------------------------------------*)
Inv3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

Invariants == Inv1 /\ Inv2 /\ Inv3

Properties == <<Inv1, Inv2, Inv3>>

====