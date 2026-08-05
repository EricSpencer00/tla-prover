---- MODULE ReachableProofs ----
EXTENDS Naturals

CONSTANTS Nodes, Root

ASSUME Root \in Nodes

Neighbors(n) == { m \in Nodes : m >= n /\ m # n }

VARIABLES mark, frontier, pc
vars == <<mark, frontier, pc>>

RECURSIVE ReachSet(_)
ReachSet(S) == IF S = {} THEN {}
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN ReachSet(S \ {x}) \cup Neighbors(x)

RECURSIVE ReachFrom(_)
ReachFrom(N) == ReachSet({N})

\* Invariant 1 is the inductive type-correctness plus a basic closure
\* property; Invariant 2 restates Lemma 1 as an inductive hypothesis.
TypeOK ==
  /\ mark \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start","run","done"}
  /\ frontier \subseteq ReachSet(mark \cup frontier)
  /\ \A x \in mark : Neighbors(x) \subseteq (mark \cup frontier)

Init ==
  /\ mark = {Root}
  /\ frontier = {}
  /\ pc = "start"

Expand ==
  /\ pc = "start"
  /\ pc' = "run"
  /\ UNCHANGED <<mark, frontier>>

\* The non-empty frontier and the non-saturated closure are dual guards.
PickFrontier ==
  /\ frontier = {}
  /\ \E n \in Nodes \ mark : frontier' = {n}
  /\ UNCHANGED <<mark, pc>>

MarkFrontier ==
  /\ frontier # {}
  /\ frontier \cap mark = {}
  /\ \A x \in mark : Neighbors(x) \subseteq (mark \cup frontier)
  /\ mark' = mark \cup frontier
  /\ frontier' = {}
  /\ UNCHANGED pc

Saturate ==
  /\ frontier = {}
  /\ \A x \in mark : Neighbors(x) \subseteq mark
  /\ pc' = "done"
  /\ UNCHANGED <<mark, frontier>>

Next ==
  \/ Expand
  \/ PickFrontier
  \/ MarkFrontier
  \/ Saturate

Spec == Init /\ [][Next]_vars

Invariant1 == TypeOK

\* Lemma 1 restated as an inductive hypothesis over the algorithm's state.
Invariant2 == ReachFrom(mark) \cup ReachFrom(frontier) = ReachFrom(mark \cup frontier)

\* Lemma 2 and Lemma 3 together give the final correctness claim.
Invariant3 == ReachFrom(Root) = mark \cup ReachFrom(frontier)

\* The algorithm's partial correctness: on termination the marked set is
\* exactly the set of reachable nodes.
PartialCorrectness == (pc = "done") => (ReachFrom(Root) = mark)
====