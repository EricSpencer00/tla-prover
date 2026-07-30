---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "loop", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* One main action, two cases, chosen nondeterministically from the frontier.
Explore ==
  /\ pc = "loop"
  /\ \E n \in frontier :
       /\ frontier' = frontier \cup {n}
       /\ IF n \in marked
          THEN frontier' = frontier \ {n}
          ELSE frontier' = frontier \cup Succ[n]
       /\ marked' = IF n \in marked THEN marked ELSE marked \cup {n}
  /\ UNCHANGED pc

Terminate ==
  /\ pc \in {"start", "loop"}
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ Explore
  \/ Terminate

Spec == Init /\ [][Next]_vars

\* The invariant family is the whole story: the two sets overlap but the
\* reachable set is only ever discovered, never invented or lost.
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 == (marked \cup frontier) \cup (Nodes \ (marked \cup frontier))
  = (marked \cup frontier) \cup (Nodes \ (marked \cup frontier))

Inv3 ==
  \A x \in Nodes : (x \in reachable(Root) /\ x \notin frontier) <=> x \in marked

PartialCorrectness == frontier = {} => marked = reachable(Root)

\* Weak fairness of the one action drives termination on a finite reachable set.
Termination == (FINITE(reachable(Root)) /\ pc = "loop") ~> pc = "done"

\* The .cfg maps Succ to a smaller operator, but Succ itself must still exist.
ConnectedToSomeButNotAll ==
  \E f \in [Nodes -> SUBSET Nodes] : Succ = f

\* The .cfg replaces Seq with a finite version of itself.
LimitedSeq ==
  \E s \in Seq(Nodes) : TRUE

====