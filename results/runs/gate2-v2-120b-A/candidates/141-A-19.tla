---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES visited, frontier, pc

\* ----------------------------------------------------------------------
\* Definitions
\* ----------------------------------------------------------------------
Bool :: {"Running", "Done"}

\* Helper definition of the set of nodes reachable from a given set of nodes
ReachableFrom(S) == 
  \* Compute the least fixed point of expanding S by successors
  LET
    Expand(T) == T \cup { y \in Nodes : \E x \in T : y \in Succ[x] }
  IN
    CHOOSE R \in SUBSET Nodes :
      /\ T = S
      /\ \A n \in Nat :
           LET Tn == 
                IF n = 0 THEN S
                ELSE Expand(TnMinus1)
           IN Tn = R
      /\ \A y \in R : \E x \in S : y \in SuccStar[x]

\* For readability we also define the set of nodes reachable from the root
ReachRoot == ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Process ==
  /\ pc = "Running"
  /\ frontier # {}
  /\ \E n \in frontier :
      IF n \notin visited THEN
        /\ visited' = visited \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc' = "Running"
      ELSE
        /\ visited' = visited
        /\ frontier' = frontier \ {n}
        /\ pc' = "Running"

Terminate ==
  /\ pc = "Running"
  /\ frontier = {}
  /\ visited' = visited
  /\ frontier' = frontier
  /\ pc' = "Done"

Next ==
  \/ Process
  \/ Terminate
  \/ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<visited, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in Bool

Inv1 == 
  \A n \in visited : \A s \in Succ[n] : s \in visited \/ s \in frontier

Inv2 ==
  \A S \in SUBSET Nodes :
    (ReachableFrom(visited) \cup ReachableFrom(frontier)) =
    ReachableFrom(visited \cup frontier)

Inv3 ==
  ReachableFrom({Root}) = visited \cup ReachableFrom(frontier)

PartialCorrectness ==
  /\ pc = "Done"
  /\ visited = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == [](pc = "Done")

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by the cfg but useful for sanity)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====