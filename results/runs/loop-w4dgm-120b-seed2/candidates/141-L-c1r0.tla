---- MODULE Reachable ----
EXTENDS Integers, Sequences

CONSTANT Nodes, Root, Succ

SuccessorSet(x) == UNION {Succ[n] : n \in x}

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"loop", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "loop"

Explore(p) ==
  \/ IF p \notin marked
       THEN /\ marked' = marked \cup {p}
            /\ frontier' = frontier \cup Succ[p]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {p}
  /\ pc' = IF frontier = {} THEN "done" ELSE "loop"

Next ==
  /\ pc = "loop"
  /\ frontier # {}
  /\ \E p \in frontier : Explore(p)

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in marked : {m \in Nodes : \E o \in Succ[n] : m = o} \subseteq (marked \cup frontier)

Inv2 ==
  SuccessorSet(marked \cup frontier) \cup (marked \cup frontier) = SuccessorSet(marked) \cup SuccessorSet(frontier)

Inv3 ==
  Nodes = (marked \cup SuccessorSet(frontier)) \cup (frontier \cup SuccessorSet(marked))

PartialCorrectness ==
  (pc = "done") => (Nodes = marked)

Termination ==
  \A p \in frontier : TRUE
  /\ \A p \in frontier : Explore(p)
  /\ (\E p \in frontier : Explore(p))

ConnectedToSomeButNotAll(f, n) == {m \in Nodes : m \in f[n]}
LimitedSeq(f) == [n \in Nodes |-> ConnectedToSomeButNotAll(f, n)]

====