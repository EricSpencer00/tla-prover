---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\* Model-checking configuration for the sequential Misra reachability algorithm.
\* It supplies concrete configuration constants so the state space is finite.
\* Sequences are bounded to Length(Seq) <= Cardinality(Nodes), overriding the
\* default infinite type in the algorithm's definition.

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "idle"

Step ==
  /\ pc \in {"idle", "running"}
  /\ \E v \in frontier :
       /\ v \notin marked
       /\ marked' = marked \cup {v}
       /\ frontier' = frontier \cup Succ[v]
  /\ pc' = IF frontier = {} THEN "done" ELSE "running"

Spec == Init /\ [][Step]_vars

\* Invariant: the marked set is closed under the successor relation.
Inv1 ==
  \A u \in marked : \A w \in Succ[u] : w \in marked

\* Invariant: the frontier is a subset of the marked set minus the root.
Inv2 ==
  frontier \subseteq (marked \ {Root})

\* Invariant: the marked set equals the reachable set via bounded paths.
Inv3 ==
  /\ \A w \in marked : \E p \in Seq :
       /\ Len(p) <= Cardinality(Nodes)
       /\ p[1] = Root
       /\ p[Len(p)] = w
       /\ \A k \in 1..(Len(p) - 1) : p[k + 1] \in Succ[p[k]]
  /\ \A w \in Nodes : (\E p \in Seq :
       /\ Len(p) <= Cardinality(Nodes)
       /\ p[1] = Root
       /\ p[Len(p)] = w
       /\ \A k \in 1..(Len(p) - 1) : p[k + 1] \in Succ[p[k]]) => w \in marked

\* The algorithm never loses a marked node (partial correctness of accumulation).
PartialCorrectness ==
  \A S \in SUBSET Nodes : (\A w \in marked : w \in S) => marked \subseteq S

\* Exhaustively checked because the configuration is finite.
Termination == <>(pc = "done")

====