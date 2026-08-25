---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Concrete graph: each node has exactly two successors.
\* The .cfg substitutes the identifier Succ with ConnectedToSomeButNotAll,
\* so we provide the overridden definition here.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll == 
  [ n \in Nodes |-> 
        CASE n = 1 -> {2,3}
      [] n = 2 -> {3,4}
      [] n = 3 -> {1,4}
      [] n = 4 -> {1,2}
      [] OTHER -> {} ]

\* ----------------------------------------------------------------------
\* LimitedSeq: a finite version of Seq bounded by the number of nodes.
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(S) }

\* ----------------------------------------------------------------------
\* State variables (inherited from the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definition of the set of nodes reachable from Root via
\* paths of bounded length (using the limited sequence operator).
\* ----------------------------------------------------------------------
ReachableFromRoot == 
  { n \in Nodes :
      \E s \in LimitedSeq(Nodes) :
        /\ Len(s) > 0
        /\ s[1] = Root
        /\ s[Len(s)] = n
        /\ \A i \in 1..Len(s)-1 : s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  }

\* ----------------------------------------------------------------------
\* Initial state (inheritance from the algorithm specification)
\* ----------------------------------------------------------------------
Init == 
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "step"

\* ----------------------------------------------------------------------
\* Next-state relation (standard BFS‑style step of the sequential algorithm)
\* ----------------------------------------------------------------------
Step == 
  /\ pc = "step"
  /\ LET newMarked == marked \cup frontier IN
     LET newFrontier == 
          (UNION { ConnectedToSomeButNotAll[n] : n \in frontier })
          \ newMarked
     IN
        /\ marked' = newMarked
        /\ frontier' = newFrontier
        /\ pc' = IF newFrontier = {} THEN "done" ELSE "step"

Done == 
  /\ pc = "done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == Step \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file
\* ----------------------------------------------------------------------
TypeOK == 
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"step", "done"}

Inv1 == 
  \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

Inv2 == 
  frontier \subseteq ReachableFromRoot \ marked

Inv3 == 
  marked \subseteq ReachableFromRoot

PartialCorrectness == 
  pc = "done" => marked = ReachableFromRoot

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

====