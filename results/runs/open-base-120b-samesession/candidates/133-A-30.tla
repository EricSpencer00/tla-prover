---- MODULE MCParReach ----
EXTENDS Sequences, FiniteSets, Naturals, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Helper to compute the next index cyclically within the set Nodes *)
SuccIdx(i) == (i % Cardinality(Nodes)) + 1

(* Bounded successor relation: each node has exactly two successors *)
ConnectedToSomeButNotAll(n) == { SuccIdx(n), SuccIdx(SuccIdx(n)) }

(* Finite sequences limited to length at most the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification and properties, reusing definitions from the parallel algorithm *)
Spec == ParSpec
Inv == ParInv
Refines == ParRefines

====