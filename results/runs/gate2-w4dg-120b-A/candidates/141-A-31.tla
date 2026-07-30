---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE x \in S : TRUE
           rest == S \ {n}
       IN {n} \cup ReachFrom(rest \cup Succ[n])

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "halted"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(n) ==
  \/ /\ n \notin marked
     /\ marked' = marked \cup {n}
     /\ frontier' = frontier \cup Succ[n]
  \/ /\ n \in marked
     /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Next ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier : Explore(n)
  /\ pc' = IF frontier = {Root} /\ n \in marked THEN "halted" ELSE pc

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A m \in marked : Succ[m] \subseteq (marked \cup frontier)

Inv2 ==
  ReachFrom(marked \cup frontier) = ReachFrom(marked) \cup ReachFrom(frontier)

Inv3 ==
  ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
  (pc = "halted") => (marked = ReachFrom({Root}))

Termination ==
  (Cardinality(ReachFrom({Root})) < Cardinality(Nodes))
    ~> (pc = "halted")

====