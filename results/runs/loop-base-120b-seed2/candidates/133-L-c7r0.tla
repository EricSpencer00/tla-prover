---- MODULE MCParReach ----
EXTENDS Sequences, FiniteSets, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete definitions for the configuration *)
Nodes == 1..4
Root  == 1
Procs == 1..2

Succ == [ n \in Nodes |-> 
            IF n = 1 THEN {2,3}
            ELSE IF n = 2 THEN {3,4}
            ELSE IF n = 3 THEN {4,1}
            ELSE {1,2} ]

(* Operator that will be substituted for Succ in the cfg *)
ConnectedToSomeButNotAll(node) == Succ[node]

(* Bounded‑length sequence operator that replaces Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Expose the core specification operators from the parallel algorithm *)
Spec    == ParReach!Spec
Init    == ParReach!Init
Next    == ParReach!Next
Inv     == ParReach!Inv
Refines == ParReach!Refines

====