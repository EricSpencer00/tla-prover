---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ frontier # {}
  /\ pc = "running"
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup (ReachableFrom(frontier, Succ)) =
    ReachableFrom(marked \cup frontier, Succ)

Inv3 ==
  ReachableFrom({Root}, Succ) = marked \cup ReachableFrom(frontier, Succ)

PartialCorrectness ==
  (pc = "done") => (marked = ReachableFrom({Root}, Succ))

Termination ==
  /\ \A n \in Nodes : TRUE
  /\ WF_vars(Explore)

====