---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete values for the constants; the .cfg may override them. *)
ASSUME Nodes = 1..4
ASSUME Root = 1
ASSUME Procs = 1..2

(* Succ will be replaced by ConnectedToSomeButNotAll in the configuration. *)
ConnectedToSomeButNotAll(n) ==
    CASE n = 1 -> {2, 3}
    []  n = 2 -> {3, 4}
    []  n = 3 -> {4, 1}
    []  OTHER -> {1, 2}

(* A finite version of Seq, limited by the number of nodes. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* The main specification, inheriting Init and Next from ParReach. *)
Spec == Init /\ [][Next]_vars

(* Inductive invariant: type correctness plus a simple control‑flow condition. *)
Inv ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A p \in Procs : pc[p] \in {"idle", "busy", "done"}

(* Refinement property stating that the parallel algorithm implements the
   sequential Misra algorithm.  Here we keep it as a placeholder. *)
Refines == TRUE

====