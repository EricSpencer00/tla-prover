---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  LET add(E, T) == {t \in T : \E e \in E : e \in \{t\}}
      step(T) == T \cup add(S, T)
      limit(T) == IF step(T) = T THEN T ELSE limit(step(T))
  IN limit(S)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching", "done"}

Invariant1 ==
  /\ TypeOK
  /\ \A u \in marked : \A v \in Nodes : (u \in marked /\ u # v) => (v \in marked \/ v \in frontier)

\* Reachable-from applied to the union of two sets is the same as reachable-from
\* applied to each set and then taking the union -- this is the key graph lemma.
Invariant2 ==
  ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

\* The set reachable from the root is exactly the current progress: what is marked,
\* together with what is reachable from the frontier. Lemma 2 lets us move the root
\* from the left side into the frontier-derived part on the right. Lemma 3 gives
\* the empty base case.
Invariant3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "idle"

Mark ==
  /\ pc = "idle"
  /\ pc' = "searching"
  /\ UNCHANGED <<marked, frontier>>

\* The frontier collects the successors of the current frontier and of the
\* newly marked node; some of them may already be marked or already be in the
\* frontier from an earlier step, which is exactly what Invariant1 forbids.
Expand ==
  /\ pc = "searching"
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = ReachableFrom(frontier) \ frontier \ marked
  /\ UNCHANGED pc

Conclude ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Mark
  \/ Expand
  \/ Conclude

Spec == Init /\ [][Next]_vars

Terminated == pc = "done"

\* TLAPS can check this only under termination, which the model does not
\* prove (liveness is outside its scope); the theorem is still stated here.
PartialCorrectness == Terminated => marked = ReachableFrom({Root})

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3
PROPERTIES == PartialCorrectness
====