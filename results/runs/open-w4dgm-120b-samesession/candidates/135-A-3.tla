---- MODULE MCReachable ----
EXTENDS FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* k is the bound on the length of a witness sequence, overriding the
\* unbounded Seq from Sequences so the existential quantifier over paths
\* stays finite; the override is injected by the .cfg at model-check time.
Bound == Cardinality(Nodes)

VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "working", "done"}

\* Successor closure: every node in the search frontier is a successor of
\* a node that is already marked as reached.
Inv1 ==
  \A n \in frontier : \E m \in marked : n \in Succ[m]

\* Reachable set: every node reached by some bounded sequence from the
\* root is already in the marked set (no reachable node is missed).
Inv2 ==
  \A n \in Nodes :
    (\E seq \in 1..Bound : seq[1] = Root /\ seq[Bound] = n /\ \A i \in 1..Bound-1 : seq[i+1] \in Succ[seq[i]])
      => n \in marked

\* Reachable decomposition: every unmarked node has all of its successors
\* already marked (nothing reachable is left on the frontier).
Inv3 ==
  \A n \in Nodes \ marked :
    \A t \in Succ[n] : t \in marked

\* Partial correctness: every node the algorithm has marked is reachable
\* by some bounded sequence of successors from the root.
PartialCorrectness ==
  \A n \in marked :
    \E seq \in 1..Bound : seq[1] = Root /\ seq[Bound] = n /\ \A i \in 1..Bound-1 : seq[i+1] \in Succ[seq[i]]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "idle"

ExploreNode(n) ==
  /\ pc \in {"idle", "working"}
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ pc' = "working"

Complete ==
  /\ frontier = {}
  /\ pc # "done"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : ExploreNode(n)
  \/ Complete

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Termination == <>(pc = "done")

\* The configuration injects this bounded version of Succ and a bounded
\* version of Seq (LimitedSeq) so the model stays finite; the names are
\* fixed by the .cfg, so only this operator is defined here.
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(f, r) ==
  { <<i, f[i]>> : i \in 1..r }
====