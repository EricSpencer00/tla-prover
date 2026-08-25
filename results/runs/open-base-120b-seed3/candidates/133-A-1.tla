---- MODULE MCParReach ----
EXTENDS ParallelReach, Sequences

CONSTANTS Nodes, Root, Procs, Succ

(* concrete graph with 4 nodes, each having exactly 2 successors *)
Nodes == {"n1", "n2", "n3", "n4"}
Root  == "n1"
Procs == {"p1", "p2"}

(* operator that the .cfg substitutes for Succ *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
        CASE n = "n1" -> {"n2", "n3"}
        [] n = "n2" -> {"n3", "n4"}
        [] n = "n3" -> {"n4", "n1"}
        [] n = "n4" -> {"n1", "n2"} ]

(* finite version of Seq, bounded by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* specification of the parallel reachability algorithm, using the
   definitions inherited from ParallelReach *)
Spec == Init /\ [][Next]_{vars}

(* safety invariant and refinement property, re‑exported from the
   parallel algorithm module *)
Inv == ParallelReach!Inv
Refines == ParallelReach!Refines

====