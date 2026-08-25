---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* operator that substitutes for Succ in the .cfg *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* finite version of Seq for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====