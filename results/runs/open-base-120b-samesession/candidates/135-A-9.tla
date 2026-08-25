---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Bounded sequence operator for model checking
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Concrete graph: each node has exactly two successors
\* This operator will be substituted for Succ by the .cfg file
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> 
    CASE n = 1 -> {2, 3}
    [] n = 2 -> {3, 4}
    [] n = 3 -> {1, 4}
    [] n = 4 -> {1, 2}
    [] OTHER -> {}
  ]

\* ----------------------------------------------------------------------
\* State variables of the sequential Misra reachability algorithm
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

\* ----------------------------------------------------------------------
\* One step of the algorithm
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "run"
     /\ frontier # {}
     /\ LET n == CHOOSE x \in frontier
        IN /\ marked'   = marked \cup {n}
           /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
           /\ pc'       = "run"
  \/ /\ pc = "run"
     /\ frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ marked ⊆ Nodes
  /\ frontier ⊆ Nodes
  /\ pc ∈ {"run", "done"}

\* ----------------------------------------------------------------------
\* Invariant 1: successor closure
\* ----------------------------------------------------------------------
Inv1 == ∀ n \in marked : Succ[n] ⊆ marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: frontier and marked are disjoint
\* ----------------------------------------------------------------------
Inv2 == frontier ∩ marked = {}

\* ----------------------------------------------------------------------
\* Invariant 3: reachable set equality (using bounded sequences)
\* ----------------------------------------------------------------------
ReachableSet ==
  { n \in Nodes :
      ∃ s \in LimitedSeq :
        /\ Len(s) > 0
        /\ Head(s) = Root
        /\ Last(s) = n
        /\ \A i \in 1..(Len(s)-1) : s[i+1] \in Succ[s[i]]
  }

Inv3 == marked \cup frontier = ReachableSet

\* ----------------------------------------------------------------------
\* Partial correctness: when algorithm terminates, all reachable nodes are marked
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "done") => (marked = ReachableSet)

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES  == Termination

====