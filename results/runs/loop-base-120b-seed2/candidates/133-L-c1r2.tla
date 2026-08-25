---- MODULE MCParReach ----
EXTENDS Sequences, Naturals, TLC, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Operator substituted for Succ in the configuration *)
ConnectedToSomeButNotAll == Succ

(* Finite version of Seq, bounded by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Top‑level identifiers required by the configuration *)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines

====