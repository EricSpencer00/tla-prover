---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Nodes, Root, Succ

\* The model is a concrete configuration of the Misra reachability algorithm: a
\* fixed small graph (Nodes, Succ) and a bound that makes sequences finite.

\* Reachability is defined by the existence of a node sequence from the root to
\* a candidate node; the SupplementaryBound turns the otherwise infinite sequence
\* quantifier into a finite one so the model is checkable.

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "searching", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "init"

StartSearch ==
  /\ pc = "init"
  /\ pc' = "searching"
  /\ UNCHANGED <<marked, frontier>>

\* The algorithm always keeps the frontier subset of the marked set, and always
\* extends the marked set with successors of frontier nodes, so the frontier can
\* only shrink as new nodes are marked and reachability is explored.
Expand(n) ==
  /\ pc = "searching"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup Succ[n]
  /\ UNCHANGED pc

Complete ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ StartSearch
  \/ (\E n \in Nodes: Expand(n))
  \/ Complete

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Nodes: Expand(n)) /\ WF_vars(Complete)

\* Invariant: no frontier node is outside the marked set; unmarked nodes are always
\* outside the frontier, so a node is either discovered or not at all.
FrontierSubsetMarked ==
  frontier \subseteq marked

\* Invariant: every marked node is reachable from the root via a sequence of
\* adjacency steps (bounded length, thanks to SupplementaryBound).
ReachableViaSeq(R) ==
  \E seq \in SupplementaryBound : seq[1] = Root /\ seq[Len(seq)] = R
                                 /\ \A i \in 1..(Len(seq) - 1) : seq[i+1] \in Succ[seq[i]]

ClosedUnderAdjacency ==
  \A n \in marked : ReachableViaSeq(n)

ReachableDecomposition ==
  marked = {n \in Nodes : \E seq \in SupplementaryBound : seq[1] = Root /\ seq[Len(seq)] = n
                                          /\ \A i \in 1..(Len(seq) - 1) : seq[i+1] \in Succ[seq[i]]}

MarkedAndFrontierSame ==
  marked = frontier \cup {Root}

\* Partial correctness: the algorithm only terminates once every node is marked.
TerminatesOnlyWhenAllMarked == (pc = "done") => (marked = Nodes)

\* The bounded sequence definition: finite length, up to the number of nodes, so
\* the existential quantification in ReachableViaSeq stays within a finite range.
SupplementaryBound == {seq \in Seq(Nodes) : Len(seq) <= Cardinality(Nodes)}

Termination == <>(pc = "done")

\* The left-hand name is the identifier the .cfg file expects; the right-hand
\* operator is the concrete finite version used at runtime.
\* The .cfg file replaces the unsized Succ with this bounded, non-empty choice
\* so both the algorithm and the replacement stay valid for every node.
ConnectedToSomeButNotAll(n) == Succ[n]
LimitedSeq == SupplementaryBound

====