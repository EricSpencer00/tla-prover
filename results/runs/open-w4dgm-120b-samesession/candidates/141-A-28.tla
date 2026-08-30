---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* The overlapping frontiers are the point of the variant: Frontier is not
\* disjoint from Marked, so the two update cases below touch it differently.
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Pick == CHOOSE x \in frontier : TRUE

ProcessFrontier ==
  /\ frontier # {}
  /\ pc = "running"
  /\ IF Pick \notin marked
       THEN /\ marked' = marked \cup {Pick}
            /\ frontier' = frontier \cup Succ(Pick)
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {Pick}
  /\ UNCHANGED pc

Terminate ==
  /\ frontier = {}
  /\ pc' = "halted"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ ProcessFrontier
  \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(ProcessFrontier) /\ SF_vars(Terminate)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "halted"}

\* Every edge out of a marked node is accounted for in either set.
Inv1 ==
  \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

UnionReachable ==
  \{ n \in Nodes : \E m \in (marked \cup frontier) : n \in Succ^*(m) \}

Inv2 ==
  UnionReachable = { n \in Nodes : \E m \in marked : n \in Succ^*(m) }

\* Marked stays exactly the reachable portion once the frontier is empty.
Inv3 == marked \cup frontier = { n \in Nodes : n \in Succ^*(Root) }

PartialCorrectness ==
  (pc = "halted") => (marked = { n \in Nodes : n \in Succ^*(Root) })

Termination == (pc = "running") ~> (pc = "halted")

====