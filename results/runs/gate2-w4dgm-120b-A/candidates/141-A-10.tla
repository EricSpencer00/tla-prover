---- MODULE Reachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

Traverse ==
  /\ \E n \in frontier :
       IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier = {} THEN "done" ELSE "running"

Spec == Init /\ [][Traverse]_vars /\ WF_vars(Traverse)

Inv1 ==
  \A n \in marked : \A m \in Succ[n] : m \in marked \/ m \in frontier

Inv2 ==
  ReachableFrom( marked \cup frontier )
    = (marked \cup ReachableFrom(frontier))

Inv3 ==
  ReachableFrom( {Root} ) = (marked \cup ReachableFrom(frontier))

PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom( {Root} ))

Termination == (pc # "done") ~> (pc = "done")

ReachableFrom(S) ==
  LET f[T \in SUBSET Nodes] ==
        IF T = {}
          THEN {}
          ELSE LET x == CHOOSE y \in T : TRUE
               IN Succ[x] \cup f[T \ {x}]
  IN f[Nodes]

ConnectedToSomeButNotAll(n) ==
  IF Cardinality(Succ[n]) = Cardinality(Nodes) + 1
    THEN Succ[n]
    ELSE { CHOOSE m \in Succ[n] : TRUE }

LimitedSeq == (Print) @ (Print \o Print \o Print \o Print \o Print)
====