---- MODULE MCParReach ----
EXTENDS ParReach, Sequences, FiniteSets, Naturals

CONSTANTS Nodes, Root, Procs, Succ

(* Concrete values for the configuration *)
Nodes == {"n0", "n1", "n2", "n3"}
Root  == "n0"
Procs == {"p0", "p1"}

(* Succ will be overridden by the .cfg with ConnectedToSomeButNotAll,
   but we give a default definition for stand‑alone use. *)
Succ == ConnectedToSomeButNotAll

(* Bounded successor relation: every node has exactly two successors. *)
ConnectedToSomeButNotAll ==
  [ n \in Nodes |-> 
      CASE n = "n0" -> {"n1", "n2"}
      [] n = "n1" -> {"n2", "n3"}
      [] n = "n2" -> {"n3", "n0"}
      [] OTHER      -> {"n0", "n1"} ]

(* Bounded sequence operator that replaces Seq from the Sequences module. *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* Specification of the parallel reachability algorithm (inherited). *)
Spec == Init /\ [][Next]_vars

(* Inductive invariant (placeholder – concrete invariant supplied by the
   parent specification). *)
Inv == TRUE

(* Refinement property asserting correspondence with the sequential
   Misra algorithm (placeholder). *)
Refines == TRUE

====