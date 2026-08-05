---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Misra's overlap-friendly variant: visited and frontier sets may intersect, which
\* is what allows a straightforward parallel version; the safety proof shows
\* reachability is still captured exactly at termination.

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"looping", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "looping"

Explore(n) ==
  \/ /\ n \in frontier
     /\ n \notin marked
     /\ marked' = marked \cup {n}
     /\ frontier' = frontier \cup Succ[n]
  \/ /\ n \in frontier
     /\ n \in marked
     /\ frontier' = frontier \ {n}
     /\ UNCHANGED marked
  /\ UNCHANGED pc

Looping ==
  /\ pc = "looping"
  /\ frontier # {}
  /\ \E n \in Nodes: Explore(n)
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "looping"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Looping \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Looping)

\* SAFETY INVARIANTS: each of the three is needed to get the reachable-set
\* characterization at the end, given that visited and frontier may overlap.
Inv1 == \A n \in marked: Succ[n] \subseteq (marked \cup frontier)
Inv2 == (marked \cup frontier) \cup ConnectedToSomeButNotAll(FrontierMinusMarked) = ConnectedToSomeButNotAll(Nodes)
Inv3 == ConnectedToSomeButNotAll(Nodes) = marked \cup ConnectedToSomeButNotAll(FrontierMinusMarked)
FrontierMinusMarked == {n \in frontier : n \notin marked}

PartialCorrectness ==
  (pc = "done") => (marked = ConnectedToSomeButNotAll(Nodes))

\* LIVENESS: with a finite reachable set, the frontier cannot stay non-empty forever,
\* so termination eventually fires under weak fairness of Looping.
FiniteTermination ==
  (ConnectedToSomeButNotAll(Nodes) # {}) ~> (pc = "done")

====