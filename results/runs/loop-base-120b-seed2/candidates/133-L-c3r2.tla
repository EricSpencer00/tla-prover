---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(*--- Graph successor operator (may be overridden by the .cfg) ---*)
ConnectedToSomeButNotAll(node) ==
  IF node \in Nodes THEN Succ[node] ELSE {}

(*--- Bounded sequence operator (replaces Seq) ---*)
LimitedSeq == { s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes) }

(*--- Specification, Invariant, and Refinement properties required by the .cfg ---*)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines

====