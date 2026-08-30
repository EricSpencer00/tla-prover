---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE x \in S : TRUE IN Succ[n] \cup ReachFrom(S \ {n})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"ready", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "ready"

Leaf(n) == Succ[n] = {}
NoDups(S) == \A i, j \in 1..Cardinality(S) : S[i] = S[j] => i = j

Explore ==
  /\ frontier # {}
  /\ pc = "ready"
  /\ \E n \in frontier :
       IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Finish ==
  /\ frontier = {}
  /\ pc = "ready"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Explore
  \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

PartialCorrectness ==
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)
  /\ ReachFrom(marked \cup frontier) = marked \cup ReachFrom(frontier)
  /\ ReachFrom({Root}) = marked \cup ReachFrom(frontier)

Termination == (frontier # {}) ~> (frontier = {})

====