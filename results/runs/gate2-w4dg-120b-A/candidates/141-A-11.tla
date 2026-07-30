---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
           rest == ReachFrom(S \ {x})
       IN {x} \cup Succ[x] \cup rest

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "finished"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Step ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E x \in frontier :
       \/ /\ x \notin marked
          /\ marked' = marked \cup {x}
          /\ frontier' = frontier \cup Succ[x]
       \/ /\ x \in marked
          /\ frontier' = frontier \ {x}
          /\ marked' = marked
  /\ pc' = IF frontier' = {} THEN "finished" ELSE pc

Next == Step

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
  (pc = "finished") => (marked = ReachFrom({Root}))

Termination ==
  \A n \in Nodes : WF_vars(Step)

====