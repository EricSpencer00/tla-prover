---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

ExploreStep ==
  \E n \in frontier :
    IF n \notin marked
    THEN /\ marked' = marked \cup {n}
         /\ frontier' = frontier \cup (Succ[n])
    ELSE /\ marked' = marked
         /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier = {} THEN "terminated" ELSE "running"

Terminating ==
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][ExploreStep]_vars /\ WF_vars(ExploreStep) /\ Terminating

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) = ReachableFromSet(marked \cup frontier)

Inv3 ==
  Nodes = ReachableFromSet({Root})

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) <=> (n \in ReachableFromSet({Root}))

Termination == \A n \in Nodes : (n \in ReachableFromSet({Root})) ~> (n \in marked)

ReachableFromSet(T) ==
  LET S == Union({Iter(T, k} : k \in Nat)
  IN S

Iter(T, k) ==
  IF k = 0 THEN T
  ELSE Iter(T, k - 1) \cup Successors(Iter(T, k - 1))

Successors(U) == {m \in Nodes : \E n \in U : m \in Succ[n]}

ConnectedToSomeButNotAll == Succ

LimitedSeq == Sequences

====