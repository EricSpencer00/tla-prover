---- MODULE MCParReach ----
EXTENDS Sequences, ParReach

CONSTANTS Nodes, Root, Procs, Succ

(* ----------------------------------------------------------------------
   Graph successor relation.
   The .cfg file will replace occurrences of the constant Succ with the
   operator ConnectedToSomeButNotAll defined below.
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) == { m \in Nodes : m # n }

(* ----------------------------------------------------------------------
   Bounded sequence operator.
   Replaces the Seq operator from the Sequences module with a length‑
   bounded version to keep the model finite.
   ---------------------------------------------------------------------- *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ----------------------------------------------------------------------
   Specification and properties required by the configuration.
   They are simply re‑exposed from the parallel reachability
   specification module.
   ---------------------------------------------------------------------- *)
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====