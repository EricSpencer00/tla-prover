---- MODULE MCParReach ----
EXTENDS Sequences, FiniteSets, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete definitions for the configuration *)
ASSUME Nodes = {1, 2, 3, 4}
ASSUME Root  = 1
ASSUME Procs = {"p1", "p2"}
ASSUME Succ  = [n \in Nodes |-> ConnectedToSomeButNotAll(n)]

(* Operator that supplies the concrete successor relation.
   Each node has exactly two successors, as required. *)
ConnectedToSomeButNotAll(n) ==
  LET next  == (n % 4) + 1
      next2 == ((n + 1) % 4) + 1
  IN {next, next2}

(* Bounded version of Seq for model checking.
   Sequences are limited to length at most the number of nodes. *)
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification and properties inherited from the parallel algorithm *)
Spec    == ParReach!Spec
Inv     == ParReach!Inv
Refines == ParReach!Refines

====