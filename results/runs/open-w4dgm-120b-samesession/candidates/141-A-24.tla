---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

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
  /\ frontier # {}
  /\ \E n \in frontier :
        \/ IF n \notin marked
           THEN /\ marked' = marked \cup {n}
                /\ frontier' = frontier \cup Succ[n]
           ELSE /\ marked' = marked
                /\ frontier' = frontier \ {n}
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Explore)
        /\ WF_vars(Terminate)

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (MarkedUnion == marked \cup frontier)
  /\ (ReachableFromMarkedUnion == {n \in Nodes : \E m \in MarkedUnion : n \in ReachableFrom[m]})
  /\ ReachableFromMarkedUnion = ReachableFrom[MarkedUnion]

Inv3 ==
  ReachableFrom[Root] = (marked \cup {n \in Nodes : \E m \in frontier : n \in ReachableFrom[m]})

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Termination == pc = "done"

ReachableFrom[n] ==
  LET R(R) ==
        {n} \cup (UNION {Succ[m] : m \in R})
  IN R(n)

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(s) == s

====