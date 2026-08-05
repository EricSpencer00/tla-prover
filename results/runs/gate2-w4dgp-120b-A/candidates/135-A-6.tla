---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "running"

SuccessorClosure ==
  /\ marked = {Root} \cup frontier
  /\ frontier \subseteq UNION {Succ[n] : n \in marked}

ReachabilityDecomposition ==
  /\ marked = UNION \{ Union { Succ^{*}[n] : n \in S } : S \in SUBSET Nodes \}

ReachableSetEquality ==
  \A n \in Nodes : (n \in marked) <=> (n \in UNION \{ Union { Succ^{*}[m] : m \in S } : S \in SUBSET Nodes \})

PartialCorrectness == \A n \in Nodes : (n \in marked) => (n \in UNION \{ Succ^{*}[n] : n \in Nodes \})

NextStep ==
  /\ pc = "running"
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = UNION {Succ[n] : n \in frontier}
  /\ pc' = IF frontier' = {} THEN "done" ELSE "running"

DoneStep ==
  /\ pc = "done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == NextStep \/ DoneStep

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 == SuccessorClosure
Inv2 == ReachabilityDecomposition
Inv3 == ReachableSetEquality

Termination == <>(pc = "done")

====