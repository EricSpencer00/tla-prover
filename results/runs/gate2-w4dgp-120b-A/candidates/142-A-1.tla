---- MODULE ReachableProofs ----
EXTENDS Integers, FiniteSets

\* A formal proof module for the sequential Misra reachability algorithm.
\* The algorithm and the fundamental graph lemmas are defined in the
\* modules it extends, so this file only introduces the invariants and
\* the partial-correctness theorem that combine them.
EXTENDS Reachable, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Explore ==
  /\ frontier = {}
  /\ frontier' = {n \in Nodes : (Root \in marked \/ frontier) /\ ~Marked(n)}
  /\ pc' = "exploring"
  /\ UNCHANGED marked

Expand ==
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = {}
  /\ pc' = "idle"

Done ==
  /\ frontier = {}
  /\ \A n \in Nodes : Marked(n) => \A m \in Nodes : Edge(n, m) => Marked(m)
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Explore \/ Expand \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1: type-correctness plus the frontier invariant (every
\* successor of a marked node is already marked or waiting in frontier).
Inv1 ==
  /\ TypeOK
  /\ \A n \in Nodes : Marked(n) => \A m \in Nodes : Edge(n, m) => Marked(m) \/ frontier[m]

\* Invariant 2: the marked set together with nodes reachable from the
\* frontier accounts for everything reachable from marked \cup frontier.
Inv2 ==
  ReachableFrom(marked) \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3: nodes reachable from the root are exactly the marked set
\* plus nodes reachable from the frontier.
Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* Partial correctness: when the algorithm halts, the marked set equals
\* the set of all nodes reachable from the root.
SpecComplete ==
  (pc = "done") => (marked = ReachableFrom({Root}))

====