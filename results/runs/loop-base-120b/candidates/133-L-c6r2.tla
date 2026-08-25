---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Successor function used for model checking: each node has exactly two distinct successors. *)
ConnectedToSomeButNotAll(n) ==
  LET candidates == Nodes \ {n} IN
  CHOOSE S \in { S \in SUBSET candidates : Cardinality(S) = 2 } : TRUE

(* Finite version of Seq: sequences are bounded by the number of nodes. *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Export the required identifiers for the configuration *)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines

====