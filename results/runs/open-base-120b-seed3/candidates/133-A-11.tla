---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete configuration *)
Nodes == {1, 2, 3, 4}
Root  == 1
Procs == {1, 2}

(* Succ will be instantiated by the configuration file via this definition *)
ConnectedToSomeButNotAll == 
    [ n \in Nodes |-> 
        CASE n = 1 -> {2, 3}
          [] n = 2 -> {3, 4}
          [] n = 3 -> {1, 4}
          [] n = 4 -> {1, 2}
    ]

(* Bounded sequence operator used in place of Seq *)
LimitedSeq(S) == { seq \in Seq(S) : Len(seq) <= Cardinality(Nodes) }

(* Tuple of all state variables declared in ParReach *)
vars == << marked, frontier, pc, sel, succSet >>

(* Specification of the parallel reachability algorithm *)
Spec == Init /\ [][Next]_vars

(* Invariant and refinement property, delegated to the parallel module *)
Inv == ParReach!Inv
Refines == ParReach!Refines

====