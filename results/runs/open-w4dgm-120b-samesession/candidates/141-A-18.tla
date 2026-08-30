---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes, Root, Succ

VARIABLES visited, frontier, pc

vars == <<visited, frontier, pc>>

SuccOf(n) == IF Succ = "self" THEN {n} ELSE Succ(n)

TypeOK ==
  /\ visited \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ visited = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier:
       \/ (n \notin visited /\ visited' = visited \cup {n} /\ frontier' = frontier \cup SuccOf(n))
       \/ (n \in visited /\ frontier' = frontier \ {n})
  /\ pc' = pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<visited, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars

\* Reachable from the frontier cannot reach anything outside the combined set.
Inv1 ==
  \A n \in visited : SuccOf(n) \subseteq (visited \cup frontier)

\* The combined reach of visited and frontier is exactly the reach of their union.
Inv2 ==
  {x \in Nodes : \E y \in visited, path \in LimitedSeq(Nodes) : PathFrom(y, path, x)} \cup
    {x \in Nodes : \E y \in frontier, path \in LimitedSeq(Nodes) : PathFrom(y, path, x)} =
      {x \in Nodes : \E y \in (visited \cup frontier), path \in LimitedSeq(Nodes) : PathFrom(y, path, x)}

\* Reachable from the root is exactly visited plus the frontier's reach.
Inv3 ==
  {x \in Nodes : \E path \in LimitedSeq(Nodes) : PathFrom(Root, path, x)} =
    visited \cup
      {x \in Nodes : \E y \in frontier, path \in LimitedSeq(Nodes) : PathFrom(y, path, x)}

\* Partial correctness: the visited set is exactly the reachable set on termination.
PartialCorrectness ==
  (pc = "done") => (\A x \in Nodes : (x \in visited) <=> (\E path \in LimitedSeq(Nodes) : PathFrom(Root, path, x)))

PathFrom(a, <<>> , x) == a = x
PathFrom(a, <<b>> \o rest, x) == (b \in SuccOf(a) /\ PathFrom(b, rest, x))

Termination == (frontier # {}) ~> (frontier = {})

====