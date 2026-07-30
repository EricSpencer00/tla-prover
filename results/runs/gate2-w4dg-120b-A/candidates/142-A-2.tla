---- MODULE ReachableProofs ----
EXTENDS Naturals, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Expand(n) ==
  /\ frontier = {} /\ pc = "idle"
  /\ frontier' = {n}
  /\ pc' = "searching"
  /\ UNCHANGED marked

Mark(x) ==
  /\ pc = "searching"
  /\ frontier = {x}
  /\ x \notin marked
  /\ marked' = marked \cup {x}
  /\ frontier' = {}
  /\ pc' = "idle"

Done ==
  /\ pc = "idle"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

InitState ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Next ==
  \/ Init
  \/ \E n \in Nodes : Expand(n)
  \/ \E x \in Nodes : Mark(x)
  \/ Done

Spec == Init /\ [][Next]_vars

\* Invariant 1 is the core inductive claim that drives the other two.
Invariant1 ==
  /\ TypeOK
  /\ \A n \in marked : successors(n) \subseteq (marked \cup frontier)

\* Invariant 2 follows directly from the key graph-theoretic Lemma 1.
Invariant2 ==
  marked \cup reachableFrom(frontier) = reachableFrom(marked \cup frontier)

\* Invariant 3 uses Lemma 2 (stability of reachable-from under adding
\* successors) and Lemma 3 (reachable-from empty is empty).
Invariant3 ==
  reachableFrom(Root) = marked \cup reachableFrom(frontier)

\* Partial correctness: termination means the marked set is exactly the
\* reachable set, neither missing nodes nor adding unreachable ones.
TerminationSoundness ==
  (pc = "done") => (marked = reachableFrom(Root))

====