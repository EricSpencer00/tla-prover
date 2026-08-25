---- MODULE MCParReach ----
EXTENDS Sequences, Naturals, TLC, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete graph with four nodes, each having exactly two successors *)
Nodes == {"n1", "n2", "n3", "n4"}
Root  == "n1"
Procs == {"p1", "p2"}

Succ == [n \in Nodes |-> 
            CASE n = "n1" -> {"n2", "n3"}
            [] n = "n2" -> {"n3", "n4"}
            [] n = "n3" -> {"n1", "n4"}
            [] n = "n4" -> {"n1", "n2"}]

(* Operator substituted for Succ in the configuration *)
ConnectedToSomeButNotAll == Succ

(* Finite version of Seq, bounded by the number of nodes *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification of the system *)
Spec == ParReach!Spec

(* Inductive invariant *)
Inv == ParReach!Inv

(* Refinement property relating parallel and sequential algorithms *)
Refines == ParReach!Refines

====