---- MODULE MCParReach ----
EXTENDS Sequences, Naturals, FiniteSets, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete configuration *)
Nodes == 1..4
Root  == 1
Procs == 1..2
Succ  == [n \in Nodes |-> 
            IF n = 1 THEN {2, 3}
            ELSE IF n = 2 THEN {3, 4}
            ELSE IF n = 3 THEN {1, 4}
            ELSE {1, 2}]

(* Operator used by the .cfg to replace Succ *)
ConnectedToSomeButNotAll == Succ

(* Bounded version of Seq for model checking *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification and properties, delegated to the parallel reachability algorithm *)
Spec     == ParReach!Spec
Inv      == ParReach!Inv
Refines  == ParReach!Refines

====