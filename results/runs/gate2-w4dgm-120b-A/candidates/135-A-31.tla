---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences, Reachable

CONSTANTS Nodes, Root, Succ

\* Reachability is defined as an existential statement over sequences of nodes.
\* To make the model finite for TLC, we replace the unbounded Sequences.Seq
\* with a bounded version that only allows sequences up to the number of nodes.
LimitedSeq == [n \in 0..Cardinality(Nodes) |-> Nodes]

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "pending"

Mark(n) ==
  /\ pc = "pending"
  /\ n \in Succ[Root]
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup {n}
  /\ pc' = pc

NextFront(n, m) ==
  /\ pc = "pending"
  /\ n \in frontier
  /\ m \in Succ[n]
  /\ m \notin marked
  /\ marked' = marked \cup {m}
  /\ frontier' = (frontier \ {n}) \cup {m}
  /\ pc' = pc

Finish ==
  /\ pc = "pending"
  /\ marked = Nodes
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Mark(n)
  \/ \E n \in Nodes, m \in Nodes : NextFront(n, m)
  \/ Finish

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"pending", "done"}

\* Successor closure: every node in the frontier is a successor of some marked node.
Inv1 ==
  /\ frontier \subseteq { n \in Nodes : \E m \in marked : n \in Succ[m] }
  /\ (frontier = {} => pc = "done")

\* Every marked node is reachable from the entry point via a path of successors.
Inv2 ==
  \A n \in marked :
    \E p \in LimitedSeq :
      /\ p # {}
      /\ p[1] = Root
      /\ p[Len(p)] = n
      /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]

\* Reachable nodes are a subset of the marked set, so no reachable node is missed.
Inv3 == { n \in Nodes : \E p \in LimitedSeq :
  /\ p # {}
  /\ p[1] = Root
  /\ p[Len(p)] = n
  /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]] } \subseteq marked

\* Partial correctness: whatever is reachable has been marked.
PartialCorrectness == Inv3

Termination == <>(pc = "done")

\* The .cfg replaces Succ with a version each node has exactly 2 successors.
ConnectedToSomeButNotAll == Succ

====