---- MODULE MCParReach ----
EXTENDS Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete values for the configuration *)
Nodes == {"n1", "n2", "n3", "n4"}
Root  == "n1"
Procs == {"p1", "p2"}

Succ == [
    "n1" |-> {"n2", "n3"},
    "n2" |-> {"n3", "n4"},
    "n3" |-> {"n1", "n4"},
    "n4" |-> {"n1", "n2"}
]

(* Operator substituted for Succ *)
ConnectedToSomeButNotAll == Succ

(* Finite, length‑bounded version of Seq *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification, invariant and property exposed for the .cfg file *)
Spec    == ParReach!Spec
Inv     == ParReach!Inv
Refines == ParReach!Refines

====