---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* A bounded sequence type derived from the standard Sequences module. This FINITE
\* override forces all sequences in this model to be below a size proportional to
\* the number of nodes, which is what makes the model checkable.
LimitedSeq(S) == CHOOSE s \in { x \in Seq(S) : Len(x) <= Cardinality(Nodes) } : TRUE

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "complete"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "searching"

\* Reachability proceeds exactly as in the sequential algorithm: one frontier node
\* is chosen and all of its successors are added to both the marked and frontier
\* sets. Unlike the standard algorithm, the successor relation here is a concrete
\* constant rather than an uninterpreted relation, so reachability can be checked.
Step(n) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ frontier' = (frontier \cup ConnectedToSomeButNotAll[n]) \ {n}
  /\ marked' = marked \cup ConnectedToSomeButNotAll[n]
  /\ pc' = IF frontier \ {n} = {} THEN "complete" ELSE "searching"

Done == pc = "complete"

Next == \E n \in Nodes : Step(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Done)

\* The closure property: any successor of a marked node must itself be marked.
Inv1 == \A n \in Nodes : n \in marked => ConnectedToSomeButNotAll[n] \subseteq marked

\* The decomposition property: every node is either marked or reachable from the
\* frontier in one backward step. Because the graph is built from the constant
\* ConnectedToSomeButNotAll, this is a concrete, checkable condition.
Inv2 == \A n \in Nodes :
  n \in marked
    \/ (\E f \in frontier : n \in ConnectedToSomeButNotAll[f])
    \/ (n = Root /\ frontier = {})

\* Reachability via a bounded path: the set of nodes reachable forward from the
\* frontier, using only sequences short enough to fit within the model bound,
\* equals the set of marked nodes.
Inv3 ==
  \A n \in Nodes :
    n \in marked <=>
      (\E seq \in LimitedSeq(Nodes) :
         /\ \A i \in 1..(Len(seq) - 1) : seq[i+1] \in ConnectedToSomeButNotAll[seq[i]]
         /\ seq[1] \in frontier
         /\ seq[Len(seq)] = n)

PartialCorrectness == Root \in marked

Termination == <>Done

====