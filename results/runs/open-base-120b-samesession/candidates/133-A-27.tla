---- MODULE MCParReach ----
EXTENDS ParallelReachability, Sequences

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete definitions for the configuration *)
Nodes == {"n1", "n2", "n3", "n4"}
Root  == "n1"
Procs == {"p1", "p2"}

(* Succ will be replaced by the operator ConnectedToSomeButNotAll via the .cfg file.
   We still declare it as a constant so that the constant list matches the configuration. *)

(* Replacement for the successor relation; each node has exactly two successors. *)
ConnectedToSomeButNotAll ==
    [node \in Nodes |-> 
        CASE node = "n1" -> {"n2","n3"},
             node = "n2" -> {"n3","n4"},
             node = "n3" -> {"n1","n4"},
             node = "n4" -> {"n1","n2"}]

(* A finite version of Seq that bounds the length of sequences to the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* The specification, invariant, and refinement property are inherited from the
   parallel reachability algorithm.  They are exported here under the required names. *)
(* Spec, Inv, and Refines are assumed to be defined in ParallelReachability. *)

====