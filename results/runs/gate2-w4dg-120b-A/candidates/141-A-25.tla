---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

Explore ==
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier = {} THEN "done" ELSE "run"

Next == Explore

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Explore)

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup (UNION {Succ[n] : n \in frontier}) =
    marked \cup (UNION {Succ[n] : n \in frontier \cup marked})

Inv3 ==
  (marked \cup frontier) \cup (UNION {Succ[n] : n \in frontier}) =
    (marked \cup frontier) \cup (UNION {Succ[n] : n \in frontier \cup marked})

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) <=> (\E p \in Seq : Root #> n)

Termination == (UNION {Succ[n] : n \in reachable}) \subseteq Nodes => <> (pc = "done")

====