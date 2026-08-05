---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ReachableFrom(_, _)
ReachableFrom(N, S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
       IN (N[x] \cup ReachableFrom(N, S \ {x}))
       \cup ReachableFrom(N, {y \in S : x \notin N[y]})

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ IF n \in marked
     THEN marked' = marked
     ELSE marked' = marked \cup {n}
  /\ frontier' = frontier' \cup (IF n \in marked THEN {} ELSE Succ[n])
  /\ IF frontier' = {} THEN pc' = "done" ELSE pc' = pc

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
  ReachableFrom(Succ, marked \cup frontier)
    = ReachableFrom(Succ, marked) \cup ReachableFrom(Succ, frontier)

Inv3 ==
  ReachableFrom(Succ, {Root}) = marked \cup ReachableFrom(Succ, frontier)

PartialCorrectness ==
  pc = "done" => marked = ReachableFrom(Succ, {Root})

Termination ==
  (ReachableFrom(Succ, {Root}) \subseteq Nodes)
    ~> (pc = "done")

SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT Inv1
INVARIANT Inv2
INVARIANT Inv3
INVARIANT PartialCorrectness
PROPERTY Termination

ConnectedToSomeButAll == Nodes
LimitedSeq == {s \in Seq(Nodes) : Len(s) <= 3}

====