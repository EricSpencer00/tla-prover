---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* concrete definitions for the configuration *)
Nodes == 1..4
Root  == 1
Procs == {"p1", "p2"}

Succ == [n \in Nodes |-> 
          CASE n = 1 -> {2, 3}
               [] n = 2 -> {3, 4}
               [] n = 3 -> {1, 4}
               [] n = 4 -> {1, 2}]

(* operator that substitutes for Succ in the .cfg *)
ConnectedToSomeButNotAll(n) == Succ[n]

(* finite version of Seq for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* state variables inherited from the parallel algorithm *)
VARIABLES marked, frontier, pc, sel, succSet

(* initialization and transition relation taken from the parallel algorithm *)
Init == ParReach!Init
Next == ParReach!Next

(* complete specification *)
Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

(* invariant and refinement property *)
Inv == ParReach!Inv
Refines == ParReach!Refines

====