---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Successor operator used in place of Succ *)
ConnectedToSomeButNotAll(n) ==
  LET a == Mod(n + 1, 4) IN
  LET b == Mod(n + 2, 4) IN
    {a, b} \cap Nodes

(* Finite version of Seq for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Top‑level specification, invariant and refinement property *)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines
====