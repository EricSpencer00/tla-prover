---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

\* The configuration module for the sequential Misra reachability algorithm.
\* It defines a concrete finite graph and a bounded sequence operator so
\* that the model checking state space is finite.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* Seq above is overridden by the .cfg to a bounded version, so this
\* definition is never used in the model being checked (it is the
\* original operator being replaced, kept for reference only).
LimitedSeq(S) == Seq(S)

\* The operator on the right is introduced here and the left name is the
\* one the .cfg substitutes in: a finite bounded version of successor.
ConnectedToSomeButNotAll(n) ==
  {m \in Nodes : m \in Succ[n]}

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Inv1 ==
  /\ frontier \subseteq (marked \cup {Root})
  /\ (frontier = {} => pc = "done")
  /\ marked \subseteq Nodes

Inv2 ==
  \A n \in Nodes :
    /\ n \in frontier => \E m \in marked : n \in Succ[m]
    /\ n \notin marked => n \notin frontier

Inv3 ==
  \A n \in Nodes : n \in marked <=> (n \in frontier \/ \E m \in marked : n \in Succ[m])

PartialCorrectness ==
  \A m \in frontier : \E n \in marked : n \in Succ[m]

Spec == (Init /\ [][Step]_vars) /\ WF_vars(Finish)

Init ==
  /\ marked = {Root}
  /\ frontier = ConnectedToSomeButNotAll(Root)
  /\ pc = "idle"

Step ==
  /\ pc \in {"idle", "running"}
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = \Cup_{n \in frontier} ConnectedToSomeButNotAll(n)
  /\ pc' = "running"

Finish ==
  /\ frontier = {}
  /\ pc # "done"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Termination ==
  pc = "done"

====