---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (as required by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS Nodes, Root

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
\* The set of all nodes
AllNodes == Nodes

\* Successor relation (must be defined for the specific graph)
\* For the purpose of this module we leave it as a constant that the
\* model checker can instantiate.  It maps each node to the set of its
\* immediate successors.
CONSTANT Succ

\* ReachableFrom(S) = the set of nodes reachable from any node in S
\* using the successor relation Succ.
REACHABLE(S) ==
  LET
    Reach(s) == 
      IF s \in AllNodes THEN
        {s} \cup UNION { Reach(t) : t \in Succ[s] }
      ELSE {}
  IN UNION { Reach(s) : s \in S }

(*-----------------------------------------------------------------
  Initial state (not specified in the description, we choose a sensible one)
-----------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Loop"

(*-----------------------------------------------------------------
  Actions (not specified; we provide a generic step that mimics the
  sequential Misra reachability algorithm)
-----------------------------------------------------------------*)
Step ==
  \/ /\ pc = "Loop"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
          /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ frontier = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<marked, frontier, pc>>

Next == Step

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

(*-----------------------------------------------------------------
  Invariants (as described)
-----------------------------------------------------------------*)
\* Invariant 1: type correctness and every successor of a marked node
\* is either already marked or in the frontier.
Inv1 ==
  /\ marked \subseteq AllNodes
  /\ frontier \subseteq AllNodes
  /\ pc \in {"Loop", "Done"}
  /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Invariant 2: marked ∪ reachable(frontier) = reachable(marked ∪ frontier)
Inv2 ==
  marked \cup REACHABLE(frontier) = REACHABLE(marked \cup frontier)

\* Invariant 3: reachable from Root = marked ∪ reachable(frontier)
Inv3 ==
  REACHABLE({Root}) = marked \cup REACHABLE(frontier)

(*-----------------------------------------------------------------
  Theorem (partial correctness)
-----------------------------------------------------------------*)
THEOREM PartialCorrectness ==
  Spec => [] (pc = "Done" => marked = REACHABLE({Root}))

(*-----------------------------------------------------------------
  Exported identifiers required by the .cfg file
-----------------------------------------------------------------*)
VARIABLES marked, frontier, pc
INIT Init
NEXT Next
INVARIANT Inv1
INVARIANT Inv2
INVARIANT Inv3
THEOREM PartialCorrectness

====