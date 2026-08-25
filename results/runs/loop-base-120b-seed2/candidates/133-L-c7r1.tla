---- MODULE MCParReach ----
EXTENDS Sequences, FiniteSets, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Operator that will be substituted for Succ in the cfg *)
ConnectedToSomeButNotAll(node) == Succ[node]

(* Bounded‑length sequence operator that replaces Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====