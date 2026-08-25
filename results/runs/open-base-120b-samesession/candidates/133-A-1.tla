---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete graph definition: each node has exactly two distinct successors *)
CONSTANT Graph

ASSUME /\ Graph \in [Nodes -> SUBSET Nodes]
       /\ \A n \in Nodes : Cardinality(Graph[n]) = 2

(* Operator that will replace the abstract successor relation *)
ConnectedToSomeButNotAll(n) == Graph[n]

(* Bounded version of the sequence operator from the Sequences module *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Expose the specification and the key properties from the parallel algorithm *)
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====