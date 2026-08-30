---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ frontier # {}
  /\ pc = "running"
  \/ \E n \in frontier :
       IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in marked : \A m \in ConnectedToSomeButNotAll[n] : m \in marked \/ m \in frontier

Inv2 ==
  {n \in marked : TRUE} \cup frontier = Nodes

Terminating == frontier = {}

PartialCorrectness == Terminating => marked = Nodes

Termination == Terminating ~> Terminating

InSeq(x, s) == (\E i \in DOMAIN s : s[i] = x)

\* No change to Seq's semantics, but the .cfg replaces Seq with a bounded
\* version so the reachable-fixpoint construction stays finite.
LimitedSeq(x) == x

====