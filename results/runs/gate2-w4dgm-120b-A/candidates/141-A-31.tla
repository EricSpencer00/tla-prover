---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE
    LET n == CHOOSE x \in S : TRUE IN {n} \cup ReachableFrom(S \cup Succ[n]) \cup ReachableFrom(S \ {n})

ReachableFromRoot == ReachableFrom({Root})

Inv1 ==
  \A n \in marked : ReachableFrom({n}) \subseteq (marked \cup frontier)

Inv2 ==
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

Inv3 ==
  ReachableFromRoot = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  ReachableFromRoot = marked

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

ExploreStep(n) ==
  \/ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

Next ==
  \E n \in frontier : ExploreStep(n)

Fairness == \A n \in Nodes : SF_vars(ExploreStep(n))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

Termination ==
  /\ ReachableFromRoot # {}
  /\ \A n \in ReachableFromRoot : n \in Nodes
  /\ WF_vars(Next)

====