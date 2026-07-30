---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* The model-checking configuration for the sequential Misra reachability
\* algorithm.  It adds concrete definitions (the graph and a bounded
\* sequence override) on top of the algorithm's own specification.
\* The set of identifiers declared here must match exactly the identifiers
\* listed in the reference TLC configuration.

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"inprogress", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "inprogress"

Step ==
  /\ pc = "inprogress"
  /\ \E u \in frontier :
       /\ marked' = marked \cup Succ[u]
       /\ frontier' = frontier \cup Succ[u]
  /\ UNCHANGED pc

Complete ==
  /\ pc = "inprogress"
  /\ frontier = {}
  /\ frontier' = frontier
  /\ pc' = "done"
  /\ UNCHANGED marked

Next == Step \/ Complete

Spec == Init /\ [][Next]_vars

\* A node is reachable only by a finite path from the root, so Succ is
\* interpreted as a finite (bounded) relation rather than an unrestricted
\* successor function.
Inv1 ==
  /\ \A x \in marked : \E s \in LimitedSeq(Nodes) :
       /\ Len(s) <= Cardinality(Nodes)
       /\ s[1] = Root
       /\ s[Len(s)] = x
       /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  /\ \A x \in frontier : x \in marked

Inv2 ==
  \A x \in marked : \E y \in marked : x \in ConnectedToSomeButNotAll[y]

Inv3 ==
  \A x \in Nodes : x \in marked => (\E y \in Nodes : x \in ConnectedToSomeButNotAll[y])

PartialCorrectness == \A x \in Nodes : x \in marked => \E y \in Nodes : x \in ConnectedToSomeButNotAll[y]

Termination == <>(pc = "done")

\* Operators that the .cfg file substitutes in and overrides.
\* ConnectedToSomeButNotAll is the concrete bounded version of Succ;
\* LimitedSeq is a finite version of the infinite sequence type Seq.
ConnectedToSomeButNotAll == Succ
LimitedSeq == Seq

====