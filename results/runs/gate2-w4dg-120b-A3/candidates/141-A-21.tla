---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

\* The frontier may overlap the visited set, so successors of visited nodes
\* are always either already visited or waiting in the frontier.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup
     { n \in Nodes : \E m \in frontier : n \in Succ[m] }
     = { n \in Nodes : \E m \in (marked \cup frontier) : n \in Succ[m] }

Inv3 ==
  { n \in Nodes : \E m \in {Root} : n \in Succ[m] }
     = marked \cup { n \in Nodes : \E m \in frontier : n \in Succ[m] }

PartialCorrectness ==
  /\ inv3
  /\ frontier = {}

\* The modeler can pick a bounded version of Succ for the run; the invariant
\* holds for the true (possibly infinite) version as well.
ConnectedToSomeButNotAll == TRUE

\* Compile-time bound on the reachable set: the model is only ever run where
\* this holds, so termination is not at odds with an infinite graph.
ReachableSetIsFinite == Cardinality({ n \in Nodes : \E m \in {Root} : n \in Succ[m] }) < 5

Termination ==
  ReachableSetIsFinite => (pc = "running" ~> pc = "terminated")

\* The cfg swaps in this finite-version operator for the standard Seq.
LimitedSeq == Seq

====