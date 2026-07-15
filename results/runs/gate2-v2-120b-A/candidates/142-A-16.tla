---- MODULE ReachableProofs ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants (derived from the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Derived definitions
-----------------------------------------------------------------*)
Successors(n) == { m \in Nodes : TRUE } \ { n }   \* Placeholder: actual successor relation should be defined elsewhere

ReachableFrom(S) == 
    IF S = {} THEN {} 
    ELSE S \cup { y \in Nodes : \E x \in ReachableFrom(S) : y \in Successors(x) }

MarkedReachable == ReachableFrom(marked)

MarkedFrontierReachable == ReachableFrom(frontier)

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ marked = { Root }
    /\ frontier = {}
    /\ pc = "Done"

(*-----------------------------------------------------------------
  No actions – the algorithm is abstracted away; this module only
  contains the invariants and the partial-correctness theorem.
-----------------------------------------------------------------*)
Next == UNCHANGED << marked, frontier, pc >>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<< marked, frontier, pc >>

(*-----------------------------------------------------------------
  Invariant 1: type correctness and successor property
-----------------------------------------------------------------*)
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in marked
    /\ \A n \in marked : \A s \in Successors(n) : s \in marked \/ s \in frontier

(*-----------------------------------------------------------------
  Invariant 2: marked ∪ reachable(frontier) = reachable(marked ∪ frontier)
-----------------------------------------------------------------*)
Inv2 ==
    marked \cup MarkedFrontierReachable = ReachableFrom(marked \cup frontier)

(*-----------------------------------------------------------------
  Invariant 3: reachable(Root) = marked ∪ reachable(frontier)
-----------------------------------------------------------------*)
Inv3 ==
    ReachableFrom({Root}) = marked \cup MarkedFrontierReachable

(*-----------------------------------------------------------------
  Partial correctness theorem (derived from the invariants)
-----------------------------------------------------------------*)
PartialCorrectness ==
    (pc = "Done") => (marked = ReachableFrom({Root}))

(*-----------------------------------------------------------------
  Theorems (optional, for TLAPS)
-----------------------------------------------------------------*)
THEOREM Inv1IsInvariant == Spec => []Inv1
THEOREM Inv2IsInvariant == Spec => []Inv2
THEOREM Inv3IsInvariant == Spec => []Inv3
THEOREM PartialCorrectnessHolds == Spec => []PartialCorrectness

====