---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* The reference .cfg substitutes ConnectedToSomeButNotAll for Succ, so a
\* finite set of successors is defined as a separate operator here and
\* ConnectedToSomeButNotAll is bound to the same operator in the .cfg.
ConnectedToSomeButNotAll(n) == Succ[n]

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in Seq(Nodes)
  /\ pc \in {"active", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = "active"

Step ==
  /\ pc = "active"
  /\ frontier # <<>>
  /\ \E n \in ConnectedToSomeButNotAll(Head(frontier)) :
       /\ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = Tail(frontier) \o <<n>>
  /\ UNCHANGED pc

Done ==
  /\ pc = "active"
  /\ frontier = <<>>
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Done

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A i \in 1..Len(frontier) : frontier[i] \in marked

Inv2 ==
  \A n \in Nodes : n \in marked => \E i \in 1..Len(frontier) : frontier[i] = n

Inv3 ==
  marked = Nodes

PartialCorrectness ==
  \A n \in Nodes : n \in marked

Termination ==
  (pc = "active") ~> (pc = "done")

====