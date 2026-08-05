---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start","done"}

ReachableFrom(S) == UNION {Succ[n] : n \in S}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

Step ==
  /\ frontier # {}
  /\ pc' = "start"
  /\ (EXISTS n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
           /\ frontier' = frontier \ {n}
           /\ marked' = marked)
  /\ UNCHANGED <<pc>>

Done ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Step \/ Done
  \/ (pc = "done" /\ UNCHANGED vars)

WeakFairness ==
  \A n \in Nodes : TRUE

Spec == Init /\ [][Next]_vars /\ (TRUE UNTIL frontier = {})

Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
Inv2 == ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)
Inv3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)
PartialCorrectness == (pc = "done") => (ReachableFrom({Root}) = marked)

Termination ==
  \A S \in SUBSET Nodes : FiniteSet(S) => (ReachableFrom(S) # S) ~> (ReachableFrom(S) = S)

====