---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Succ == [n \in Nodes |-> {}] \* Placeholder: actual successors must be supplied
\* For the purpose of this module we leave Succ undefined; it will be
\* instantiated in the configuration with a concrete function mapping each
\* node to its set of successor nodes.

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MarkedSet == marked
FrontierSet == frontier

\* ----------------------------------------------------------------------
\* Reachability operators used in the invariants
\* ----------------------------------------------------------------------
\* ReachableFrom(S) returns all nodes reachable from any node in S
\* using the graph defined by Succ.  It is defined as the least fixed point
\* of adding successors.
RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  LET Next(R) == R \cup { y \in Nodes : \E x \in R : y \in Succ[x] } IN
    CHOOSE R \in SUBSET Nodes :
        /\ R \subseteq Next(R)
        /\ S \subseteq R
        /\ \A T \in SUBSET Nodes :
              /\ S \subseteq T
              /\ T \subseteq Next(T) => R \subseteq T

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
MarkFrontier ==
  /\ pc = "Loop"
  /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \ {n}
        /\ pc' = "Loop"

AddSuccessors ==
  /\ pc = "Loop"
  /\ frontier' = frontier \cup { y \in Nodes : \E x \in marked : y \in Succ[x] } \ frontier
  /\ UNCHANGED <<marked, pc>>

Terminate ==
  /\ pc = "Loop"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ MarkFrontier
  \/ AddSuccessors
  \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and every successor of a marked node
\* is either marked or in the frontier.
Inv1 ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"Loop", "Done"}
  /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Invariant 2: marked ∪ reachableFrom(frontier) = reachableFrom(marked ∪ frontier)
Inv2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3: reachableFrom({Root}) = marked ∪ reachableFrom(frontier)
Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* ----------------------------------------------------------------------
\* Theorem (partial correctness)
\* ----------------------------------------------------------------------
THEOREM PartialCorrectness ==
  \A s \in [][Next]_<<marked, frontier, pc>> :
    (s ! pc = "Done") => (marked = ReachableFrom({Root}))

\* ----------------------------------------------------------------------
\* THE SPECIFICATION and INVARIANTS (required identifiers)
\* ----------------------------------------------------------------------
Spec == Spec
INVARIANTS == Inv1 /\ Inv2 /\ Inv3
PROPERTIES == PartialCorrectness

====