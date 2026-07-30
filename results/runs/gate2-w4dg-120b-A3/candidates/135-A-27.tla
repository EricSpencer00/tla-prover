---- MODULE MCReachable ----
EXTENDS Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

RECURSIVE ASeq(_)
ASeq(n) ==
  IF n = 0 THEN <<Root>> ELSE LET s == ASeq(n - 1) IN Append(s, Root)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "start"

Explore ==
  /\ frontier # {}
  /\ pc = "exploring"
  /\ \E x \in frontier :
       /\ marked' = marked \cup {x}
       /\ frontier' = frontier \cup {x}
  /\ UNCHANGED pc

Complete ==
  /\ frontier = {}
  /\ pc = "exploring"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Spec ==
  /\ Init
  /\ [][Explore]_vars
  /\ [][Complete]_vars
  /\ (pc = "start") ~> (pc = "exploring")

Inv1 ==
  /\ frontier \subseteq marked
  /\ \A x \in marked : \E y \in frontier : y \in Succ[x]

Inv2 ==
  /\ marked \subseteq Union({Succ[x] : x \in Nodes})

Inv3 == marked = Union({Succ[x] : x \in Nodes})

PartialCorrectness == marked = Union({Succ[x] : x \in Nodes})

Termination == (pc = "exploring") ~> (pc = "done")

LimitedSeq == ASeq

ConnectedToSomeButNotAll == Succ

====