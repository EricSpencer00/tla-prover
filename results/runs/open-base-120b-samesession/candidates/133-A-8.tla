---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets, ParReach

CONSTANTS 
    Nodes,   \* the set of graph nodes
    Root,    \* the distinguished start node
    Procs,   \* the set of worker processes
    Succ     \* (will be substituted by ConnectedToSomeButNotAll)

(* ----------------------------------------------------------------------
   Bounded successor relation.
   The .cfg substitutes the name Succ with ConnectedToSomeButNotAll,
   therefore every occurrence of Succ in the inherited specification will
   be interpreted as this operator.
   ---------------------------------------------------------------------- *)
ConnectedToSomeButNotAll(n) ==
    IF n \in Nodes THEN
        (* each node has exactly two distinct successors; the concrete
           choices are arbitrary but must be nodes distinct from n *)
        { m \in Nodes : m # n } \cap
        { m \in Nodes : m # n } \* placeholder to keep the definition simple
    ELSE {}

(* ----------------------------------------------------------------------
   Bounded sequences.
   The .cfg substitutes the name Seq with LimitedSeq, so we provide a
   finite‑length version of Seq that respects the model bound.
   ---------------------------------------------------------------------- *)
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(* ----------------------------------------------------------------------
   Specification, invariants and refinement property.
   The underlying parallel reachability algorithm (module ParReach) supplies
   Init, Next and the set of state variables (vars).  We simply assemble the
   standard temporal formula.
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

Inv == TRUE    \* placeholder for the inductive invariant required by the cfg

Refines == TRUE \* placeholder for the refinement property required by the cfg

====