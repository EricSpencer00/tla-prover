---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

(*-----------------------------------------------------------------
  Constants required by the configuration
-----------------------------------------------------------------*)
CONSTANTS
    Nodes,   \* The set of all graph nodes
    Root,    \* The designated start node, assumed to be in Nodes
    Succ,    \* A function mapping each node to the set of its successors
    Seq      \* A dummy constant required by the cfg (unused)

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    marked,   \* Set of visited (marked) nodes
    frontier, \* Set of nodes pending exploration (may overlap with marked)
    pc        \* Program counter: "Loop" or "Done"

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
NodeReachableFromRoot == 
    RECURSIVE Reach(_)
    Reach(n) == 
        IF n = Root THEN {Root}
        ELSE {n} \cup UNION { Reach(s) : s \in Succ[n] }

AllReachable == Reach(Root)

(*-----------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------*)
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Loop"
    /\ Root \in Nodes
    /\ \A n \in Nodes: Succ[n] \subseteq Nodes

(*-----------------------------------------------------------------
  Main action (two nondeterministic cases)
-----------------------------------------------------------------*)
DoStep ==
    /\ pc = "Loop"
    /\ frontier # {}
    /\ \E n \in frontier:
        \/ /\ n \notin marked
              /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
              /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ pc' = "Loop"

Terminate ==
    /\ pc = "Loop"
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ DoStep
    \/ Terminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Loop", "Done"}

(*-----------------------------------------------------------------
  Safety invariants described in the natural-language text
-----------------------------------------------------------------*)
Inv1 ==
    \A n \in marked: Succ[n] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup frontier) \subseteq Nodes
    /\ AllReachable = marked \cup ReachFromSet(frontier)

Inv3 ==
    AllReachable = marked \cup ReachFromSet(frontier)

ReachFromSet(S) ==
    UNION { Reach(n) : n \in S }

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = AllReachable

(*-----------------------------------------------------------------
  Liveness property (termination)
-----------------------------------------------------------------*)
Termination == []<>(pc = "Done")

=============================================================================