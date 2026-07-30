---- MODULE ReachableProofs ----
EXTENDS Naturals, ReachabilityModule, ReachableProofsModule

CONSTANTS
  Nodes
  Root

VARIABLES
  marked
  frontier
  pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "active"

Step ==
  /\ pc = "active"
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \cup {m \in Nodes : \E p \in marked : (p, m) \in E})
                       \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

AfterTerminate ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Step
  \/ Terminate
  \/ AfterTerminate

Spec == Init /\ [][Next]_vars

\* Invariant 1: type correctness plus all successors of a marked node are in
\* the marked set or frontier.
Invariant1 ==
  /\ TypeOK
  /\ \A p \in marked : \A m \in Nodes : (p, m) \in E => (m \in marked \/ m \in frontier)

\* Invariant 2: marked plus reachable-from-frontier equals reachable-from-marked-and-frontier,
\* proved from Lemma 1.
Invariant2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3: reachable-from-root equals marked plus reachable-from-frontier,
\* proved using Lemma 2 and Lemma 3.
Invariant3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom({Root}))

====