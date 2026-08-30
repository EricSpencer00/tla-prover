---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"bfs", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "bfs"

Explore(n) ==
  /\ n \in frontier
  /\ marked' = IF n \in marked THEN marked ELSE marked \cup {n}
  /\ frontier' = IF n \in marked
                   THEN frontier \ {n}
                   ELSE frontier \cup Succ[n]
  /\ pc' = pc

Terminate ==
  /\ frontier = {}
  /\ pc = "bfs"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Terminate

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in Nodes : Explore(n))

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

RECURSIVE ReachableFrom(S)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE m \in S : TRUE IN Succ[n] \cup ReachableFrom(S \ {n})

Inv2 ==
  ReachableFrom(marked \cup frontier) = marked \cup ReachableFrom(frontier)

Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == ReachableFrom({Root}) = marked

Termination == marked = ReachableFrom({Root})

FiniteSeq(f, S) ==
  LET g[T \in SUBSET S] ==
       IF T = {} THEN <<>>
       ELSE LET x == CHOOSE y \in T : TRUE IN <<f[x]>> \o g[T \ {x}]
  IN g[S]

LimitedSeq ==
  /\ \E f \in [Nodes -> Nat] : f = Succ
  /\ \E g \in [Nodes -> SUBSET Nodes] : g = ReachableFrom
  /\ \E h \in [Nodes -> SUBSET Nodes] : h = ReachableFrom

====