---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*=== Concrete configuration ===*)
ASSUME Nodes = 1..4
ASSUME Root \in Nodes
ASSUME Procs = {"p1", "p2"}

(*=== Bounded successor relation (each node has exactly two successors) ===*)
ConnectedToSomeButNotAll ==
  [n \in Nodes |-> { (n % 4) + 1, ((n + 1) % 4) + 1 }]

(*=== Limited version of Seq: sequences of length at most |Nodes| ===*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*=== Specification, invariant, and refinement property inherited from the parallel algorithm ===*)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines

====