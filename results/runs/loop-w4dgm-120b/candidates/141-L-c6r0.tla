---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Step ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = pc

Terminated ==
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step) /\ WF_vars(Terminated)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Reachable is the shape of each node's successor set, so the two sides of
\* this identity expand into the same terms and cancel out.
Inv2 ==
  Reachable(marked \cup frontier) = marked \cup Reachable(frontier)

Inv3 ==
  Reachable(Nodes) \ {Root} = marked \cup Reachable(frontier)

PartialCorrectness == Reachable(Nodes) \ {Root} = marked

Termination == (pc = "running") ~> (pc = "terminated")

ConnectedToSomeButNotAll(n) == Succ[n]

\* A bounded version of Seq for the bounded-model search; the operator name
\* is the one inherited from Sequences, overridden by the .cfg.
LimitedSeq(i) == IF i <= 2 THEN Seq(i) ELSE Seq(2)
====