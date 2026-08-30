---- MODULE Reachable ----
EXTENDS Naturals, Sequences

\* Misra's variant of BFS: the frontier and marked nodes may overlap, which
\* is what makes the algorithm parallelizable. The reachable-set claim at the
\* end is proved through three invariants about how marked and frontier nodes
\* relate to each other's successors; the fourth is plain type checking.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "terminated"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

Explore ==
  /\ pc = "start"
  /\ frontier # {}
  /\ \E n \in frontier :
       IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ pc' = pc

Terminate ==
  /\ pc = "start"
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ marked' = marked
  /\ frontier' = frontier

Next ==
  \/ Explore
  \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

\* The three partial-correctness invariants together imply that "marked"
\* equals exactly the reachable nodes from Root once the algorithm stops.
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) = Nodes
    => (Nodes \ marked) \cup ReachableSet(Frontier) = Nodes

Inv3 ==
  \A n \in frontier : Succ[n] \subseteq (marked \cup frontier)

Inv4 ==
  ReachableSet({Root}) = (marked \cup ReachableSet(frontier))

PartialCorrectness ==
  (pc = "terminated") => (marked = ReachableSet({Root}))

Termination ==
  (ReachableSet({Root}) # Nodes) ~> (pc = "terminated")

\* These are the operators the .cfg file substitutes in, overriding the
\* standard definitions. Succ is kept finite here -- the infinite version
\* is only needed for the variant that runs without termination.
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====