---- MODULE Reachable ----
EXTENDS Naturals, Sequences
CONSTANTS Nodes, Root, Succ

ASSUME /\ Root \in Nodes
       /\ Succ \in [Nodes -> SUBSET Nodes]

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

ReachableFrom(n) ==
  UNION {ReachableFrom(x) : x \in n} \cup n

\* Misra's twist: frontier may overlap marked, so adding successors here never
\* removes the exploring node from the frontier.
Explore(n) ==
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup Succ[n]
  /\ UNCHANGED pc
ExploreMarked(n) ==
  /\ n \in marked
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED <<marked, pc>>

ExploreOne == \E n \in frontier : Explore(n) \/ ExploreMarked(n)

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ ExploreOne
  \/ Terminate

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ExploreOne)

\* Marked nodes always push their successors forward or keep them reachable.
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* The reachable frontier plus the marked frontier is exactly the reachable
\* set of their union -- frontier nodes are forward enough to cover their
\* successors, and marked nodes may be safely dropped from the reachable
\* frontier once explored.
Inv2 == ReachableFrom(frontier \cup marked) = ReachableFrom(marked) \cup ReachableFrom(frontier)

Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == pc = "done" => marked = ReachableFrom({Root})

Termination == (ReachableFrom({Root}) # Nodes) ~> (ReachableFrom({Root}) = Nodes)
====