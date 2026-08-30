---- MODULE Reachable ----
EXTENDS Integers, Sequences

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
  /\ \E n \in frontier :
       \/ IF n \notin marked
          THEN /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
          ELSE /\ marked' = marked
               /\ frontier' = frontier \ {n}
  /\ pc' = IF frontier' = {} THEN "done" ELSE pc

Terminating ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Explore \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

Inv1 ==
  \A n \in marked : \A m \in Succ[n] : m \in marked \/ m \in frontier

ReachableFrom(S) ==
  LET Reach[T \in SUBSET Nodes] ==
        IF T = {} THEN {}
        ELSE LET n == CHOOSE x \in T : TRUE
                 rest == Reach[T \ {n}]
             IN rest \cup Succ[n] \cup {n}
  IN Reach[S]

Inv2 ==
  Reach(marked \cup frontier) = marked \cup Reach(frontier)

Inv3 ==
  Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == Reach({Root}) = marked

Termination == (Reach({Root}) # {}) ~> (Reach({Root}) = {})

====