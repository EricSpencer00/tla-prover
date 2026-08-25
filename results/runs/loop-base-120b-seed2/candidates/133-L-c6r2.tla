---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Succ will be replaced by ConnectedToSomeButNotAll in the configuration. *)
ConnectedToSomeButNotAll(n) ==
    CASE n = 1 -> {2, 3}
    [] n = 2 -> {3, 4}
    [] n = 3 -> {4, 1}
    [] OTHER -> {1, 2}

(* A finite version of Seq, limited by the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Expose the required top‑level identifiers for the configuration. *)
Spec == ParReach!Spec
Inv == ParReach!Inv
Refines == ParReach!Refines

================================