---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Overridden by the cfg: a bounded version of Seq so the state space stays finite.
LimitedSeq(A) == CHOOSE s \in Seq(A) : \A x \in A : \E i \in DOMAIN s : s[i] = x

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ(Root)
  /\ pc = "idle"

\* The algorithm marks one frontier node at a time, chosen nondeterministically.
Expand(n) ==
  /\ pc = "idle"
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ(n)) \ {n}
  /\ pc' = "idle"

\* When nothing new can be reached the algorithm halts.
Finish ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Expand(n)
  \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(Finish)

TypeOK ==
  \A S \in {marked, frontier} : S \subseteq Nodes

Inv1 ==
  frontier \cap marked = {}

Inv2 ==
  marked \subseteq {LimitedSeq(Nodes)[i] : i \in DOMAIN LimitedSeq(Nodes)}

Inv3 ==
  marked \cup frontier = Nodes

PartialCorrectness ==
  frontier = {} => marked = Nodes

Termination ==
  <>(pc = "done")

\* The cfg replaces this with a bounded, dense-outdegree graph: each node leads to
\* exactly two successors (chosen deterministically so the shape is fixed).
ConnectedToSomeButNotAll == Succ

====