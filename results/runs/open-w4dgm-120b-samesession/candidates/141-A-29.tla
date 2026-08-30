---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Succ(n) == ConnectedToSomeButNotAll[n]

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(n) ==
  \/ /\ n \in frontier
     /\ n \notin marked
     /\ marked' = marked \cup {n}
     /\ frontier' = frontier \cup Succ(n)
  \/ /\ n \in frontier
     /\ n \in marked
     /\ frontier' = frontier \ {n}
     /\ marked' = marked
  /\ pc' = IF frontier = {} THEN "done" ELSE "running"

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in Nodes : n \in marked => (Succ(n) \subseteq marked \cup frontier)

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE e \in S : TRUE IN Succ(x) \cup ReachableFrom(S \ {x})

Inv2 ==
  marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Termination ==
  /\ (FinteSet(ReachableFrom({Root})) \in {"finite", "infinite"})
  /\ WF_vars(Next)

\* The .cfg replaces the operator name Seq with this finite-bounded version.
LimitedSeq(n) == CHOOSE s \in Seq(1..n) : TRUE
====