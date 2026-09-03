---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

\* Model-checking configuration for the sequential Misra reachability
\* algorithm: concrete graph, bounded sequences, and the full invariant
\* suite from the algorithm specification.
CONSTANTS Nodes, Root, Succ

\* The reachable set is defined by an existential path using a bounded
\* sequence (LimitedSeq) rather than the unbounded Seq from Sequences.
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

StartExplore ==
  /\ pc = "idle"
  /\ pc' = "running"
  /\ UNCHANGED <<marked, frontier>>

Explore ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E x \in frontier, y \in Succ[x] :
       /\ marked' = marked \cup {y}
       /\ frontier' = (frontier \ {x}) \cup {y}
  /\ UNCHANGED pc

Finish ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Reset ==
  /\ pc = "done"
  /\ pc' = "idle"
  /\ marked' = {Root}
  /\ frontier' = {Root}

Next == StartExplore \/ Explore \/ Finish \/ Reset

Spec == Init /\ [][Next]_vars

\* Invariant: marked set closed under graph successors (every successor
\* of a marked node is marked).
Inv1 ==
  \A x \in Nodes : x \in marked => Succ[x] \subseteq marked

\* Invariant: marked set contains the root and only nodes reachable from
\* it via some path, so it never grows past what is reachable.
Inv2 ==
  /\ Root \in marked
  /\ marked \subseteq { y \in Nodes : \E p \in LimitedSeq(Nodes) :
        /\ p[1] = Root
        /\ p[Len(p)] = y
        /\ \A i \in 1 .. Len(p) - 1 : p[i + 1] \in Succ[p[i]] }

\* Invariant: every node reachable from the root is eventually marked.
Inv3 ==
  \A x \in Nodes : x \in { y \in Nodes : \E p \in LimitedSeq(Nodes) :
        /\ p[1] = Root
        /\ p[Len(p)] = y
        /\ \A i \in 1 .. Len(p) - 1 : p[i + 1] \in Succ[p[i]] } => <>(x \in marked)

PartialCorrectness == Inv1 /\ Inv2 /\ Inv3

Termination == <>(pc = "done")

\* Configuration override: Succ must be a non-trivial deterministic
\* 2-successor graph on Nodes, and LimitedSeq is the bounded version of
\* Seq(Nodes) that keeps the state space finite.
SuccAssumption ==
  /\ { Cardinality(Succ[x]) : x \in Nodes } = {2}
  /\ \A x \in Nodes : Succ[x] \subseteq Nodes

\* LimitedSeq: a finite, length-bounded version of Seq(Nodes).
LimitedSeq(S) ==
  UNION { { f \in S^{n} : n \in 1 .. Cardinality(Nodes) } : TRUE }

====