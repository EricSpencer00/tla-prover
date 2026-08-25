---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Default concrete values for the configuration; the .cfg may override them *)
ASSUME Nodes = 1..4
ASSUME Root  = 1
ASSUME Procs = {"p1", "p2"}

(* ----------------------------------------------------------------------
   Bounded graph definition.
   The .cfg substitutes the constant Succ with this operator.
   Each node has exactly two distinct successors.
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> { (n % 4) + 1 , ((n + 1) % 4) + 1 } ]

(* ----------------------------------------------------------------------
   Bounded sequence operator used instead of the unrestricted Seq.
   ---------------------------------------------------------------------- *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====