---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

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
  /\ pc = "running"
  /\ frontier # {}
  /\ \E v \in frontier :
       \/ IF v \notin marked
          THEN /\ marked' = marked \cup {v}
               /\ frontier' = frontier \cup Succ(v)
          ELSE /\ marked' = marked
               /\ frontier' = frontier \ {v}
  /\ pc' = "running"

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

Inv1 ==
  \A v \in marked : Succ(v) \subseteq marked \cup frontier

Inv2 ==
  (marked \cup frontier) \cup
    UNION {Succ(u) : u \in frontier} =
  marked \cup UNION {Succ(u) : u \in marked \cup frontier}

Inv3 ==
  Nodes \ frontier =
    marked \cup UNION {Succ(u) : u \in frontier}

PartialCorrectness ==
  \A v \in Nodes : v \in marked => \E u \in marked : v \in Succ(u)
  /\ \A v \in frontier : v \notin marked

Termination ==
  \A e \in {Explore} : e ~> (pc = "done")

====