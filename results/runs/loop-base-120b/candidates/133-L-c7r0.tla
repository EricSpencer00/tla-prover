---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* concrete definitions for the constants *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root  = 1
ASSUME Procs = {"p1", "p2"}

(* each node has exactly two successors *)
ASSUME Succ = [n \in Nodes |-> 
                 CASE n = 1 -> {2, 3}
                  [] n = 2 -> {3, 4}
                  [] n = 3 -> {4, 1}
                  [] n = 4 -> {1, 2}]

(* operator that will replace Succ in the configuration *)
ConnectedToSomeButNotAll(node) == Succ[node]

(* a finite version of Seq, limited by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* specification, invariants and refinement property are inherited *)
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====