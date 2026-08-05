---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* Misra's BFS variant: the marked and frontier sets may overlap, which
\* is what makes it parallelizable. When the frontier is empty the
\* reachable set has been fully explored.

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The frontier is explored nondeterministically, and a node may be
\* revisited (still in the frontier) after it has been marked.
Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ UNCHANGED pc
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ UNCHANGED <<marked, pc>>
  /\ pc' = IF frontier' = {} THEN "done" ELSE pc

Next == Explore

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Explore)

\* A marked node's successors are never lost: they're either already
\* marked or still waiting in the frontier.
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The reachable set is partitioned by the frontier/marked frontier.
Inv2 ==
  {r \in Nodes : \E f \in frontier : \E k \in Nat :
     \A i \in 1..k : f = r
     /\ ((k = 1) \/ (\E j \in 1..(k - 1) : Succ[r] = {r}))
     /\ \A i \in 1..k : r \in frontier
  } \cup frontier = {r \in Nodes : \E f \in marked \cup frontier : \E k \in Nat :
     \A i \in 1..k : f = r
     /\ ((k = 1) \/ (\E j \in 1..(k - 1) : Succ[r] = {r}))
  }

\* The reachable set is exactly the marked nodes plus whatever the
\* frontier still stands for.
Inv3 ==
  {r \in Nodes : \E f \in {Root} : \E k \in Nat :
     \A i \in 1..k : f = r
     /\ ((k = 1) \/ (\E j \in 1..(k - 1) : Succ[r] = {r}))
  } = marked \cup frontier

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

\* With a finite reachable set the frontier cannot stall forever: each
\* cycle either grows the finite marked set or shrinks the frontier.
Termination ==
  frontier # {} ~> frontier = {}

====