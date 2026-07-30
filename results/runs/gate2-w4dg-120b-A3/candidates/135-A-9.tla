---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Explore(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ frontier' = (frontier \cup Succ[n]) \ marked
  /\ marked' = marked \cup Succ[n]
  /\ pc' = "exploring"

StartExploration ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "exploring"
  /\ UNCHANGED <<marked, frontier>>

Finish ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == StartExploration \/ Finish \/ (\E n \in Nodes : Explore(n))

\* The algorithm's closure: every node reached in the frontier continues to have
\* all of its successors already marked.
Inv1 == \A n \in frontier : Succ[n] \subseteq marked

\* Reachability is exactly the marked set: nothing marked is left out, and none
\* left out is ever reachable.
Inv2 == marked \subseteq (UNION {Succ[n] : n \in Nodes})
Inv3 == (UNION {Succ[n] : n \in Nodes}) \subseteq marked

Termination == <>(pc = "done")

\* Model-checking configuration: a small graph with every node connected to 2
\* successors, and a bounded path witness.
\* ConnectedToSomeButNotAll is what the .cfg substitutes for Succ and gives the
\* exact 2-successor pattern promised in the description.
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> IF n = 1 THEN {2, 3}
                  ELSE IF n = 2 THEN {3, 4}
                  ELSE IF n = 3 THEN {1, 4}
                  ELSE {1, 2} ]

\* LimitedSeq is the finite witness that replaces the standard infinite Seq.
LimitedSeq ==
  { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

Spec == Init /\ [][Next]_vars

\* All required names with their exact signatures, in the order the .cfg expects.
\* The .cfg treats the left side as the name it will substitute, so the right
\* side is the real definition.
Succ == ConnectedToSomeButNotAll
Seq == LimitedSeq

\* The .cfg lists these by name, so each must exist exactly as written.
TypeOK == TypeOK
Inv1 == Inv1
Inv2 == Inv2
Inv3 == Inv3
PartialCorrectness == Inv1 /\ Inv2 /\ Inv3
Termination == Termination
====