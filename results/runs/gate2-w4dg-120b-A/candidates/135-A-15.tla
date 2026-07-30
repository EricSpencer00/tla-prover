---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES frontier, marked, pc

vars == <<frontier, marked, pc>>

\* Types: frontier and marked are bounded subsets of Nodes, pc is a bounded
\* counter, and Seq is a bounded sequence of nodes (overridden to be finite).
TypeOK ==
  /\ frontier \in SUBSET Nodes
  /\ marked \in SUBSET Nodes
  /\ pc \in 0..3
  /\ Seq \in Seq(Nodes)

Init ==
  /\ frontier = {Root}
  /\ marked = {Root}
  /\ pc = 0

Step1 ==
  /\ pc = 0
  /\ pc' = (pc + 1) % 4
  /\ frontier' = frontier
  /\ marked' = marked

Step2 ==
  /\ pc = 1
  /\ frontier # {}
  /\ \E v \in frontier : \E w \in Succ[v] :
        /\ w \notin marked
        /\ marked' = marked \cup {w}
        /\ frontier' = (frontier \cup {w}) \ {v}
  /\ pc' = (pc + 1) % 4

Step3 ==
  /\ pc = 2
  /\ frontier = {}
  /\ pc' = (pc + 1) % 4
  /\ frontier' = frontier
  /\ marked' = marked

Step4 ==
  /\ pc = 3
  /\ frontier = {}
  /\ pc' = 0
  /\ frontier' = frontier
  /\ marked' = marked

Next == Step1 \/ Step2 \/ Step3 \/ Step4

Spec == Init /\ [][Next]_vars

\* Each node has exactly 2 successors, so every visited node was reached by
\* a chain of edges from the root.
Inv1 ==
  \A v \in marked : \E p \in Seq :
    /\ Len(p) <= Cardinality(Nodes)
    /\ p[1] = Root
    /\ p[Len(p)] = v
    /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]

Inv2 ==
  \A u \in marked :
    \/ u \in frontier
    \/ frontier \cap Succ[u] # {}

\* Reachable nodes are exactly the marked nodes.
Inv3 ==
  \A u \in Nodes : u \in frontier => u \in marked

PartialCorrectness ==
  frontier = {} => marked = Nodes

Termination == <>(frontier = {})

====