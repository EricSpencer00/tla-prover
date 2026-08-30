---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachProofs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = 0

\* The marking step: a frontier node settles into the marked set and removes
\* itself from the frontier in the same step, so the two can never both hold
\* the same node and no reachable node is ever dropped from both.
Mark ==
  /\ pc = 0
  /\ \E n \in frontier :
       /\ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \ {n}
  /\ pc' = 0

Expand ==
  /\ pc = 0
  /\ \E n \in marked :
       \E m \in Nodes :
         /\ m \in Succ(n)
         /\ m \notin marked
         /\ m \notin frontier
         /\ frontier' = frontier \cup {m}
  /\ pc' = 0
  /\ marked' = marked

Quiet ==
  /\ pc = 0
  /\ marked = Nodes
  /\ frontier = {}
  /\ pc' = 1
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ pc = 1
  /\ pc' = 0
  /\ UNCHANGED <<marked, frontier>>

Next == Mark \/ Expand \/ Quiet \/ Done

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {0, 1}
  /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier

\* Invariant 1: type plus the frontier-drawing condition (the guarded subset
\* in the description) is inductive, so it holds in every reachable state.
Invariant1 == TypeOK

\* Invariant 2: level 1 of the reachable-set decomposition is preserved.
Invariant2 == ReachDecompose1

\* Invariant 3: level 2 of the reachable-set decomposition is preserved.
Invariant3 == ReachDecompose2

PartialCorrect == (pc = 1) => (Reachable(Root) = marked)

====