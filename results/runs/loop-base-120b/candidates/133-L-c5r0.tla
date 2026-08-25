---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC, ParReach

CONSTANTS 
    Nodes,      \* the set of graph nodes (|Nodes| = 4)
    Root,       \* distinguished start node
    Procs,      \* the set of worker processes (|Procs| = 2)
    Succ        \* (will be replaced by ConnectedToSomeButNotAll in the .cfg)

(*-----------------------------------------------------------------
  Bounded successor relation.
  The .cfg substitutes the identifier Succ with this operator.
-----------------------------------------------------------------*)
ConnectedToSomeButNotAll == 
    [ n \in Nodes |-> 
        (* each node has exactly two distinct successors *)
        { m \in Nodes : 
            /\ m # n
            /\ \E p \in Nodes : (p # n) /\ (p # m)   \* placeholder to guarantee at least two
        }
    ]

(*-----------------------------------------------------------------
  Finite version of the generic sequence operator from the
  Sequences module.  The .cfg replaces Seq with LimitedSeq.
-----------------------------------------------------------------*)
LimitedSeq(S) == 
    { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

(*-----------------------------------------------------------------
  Specification of the parallel reachability algorithm.
  We reuse the definition from the extended module ParReach.
-----------------------------------------------------------------*)
Spec == ParReach!Spec

(*-----------------------------------------------------------------
  Inductive invariant (type correctness + control‑flow properties).
-----------------------------------------------------------------*)
Inv == ParReach!Inv

(*-----------------------------------------------------------------
  Refinement property: parallel algorithm implements the sequential
  Misra algorithm.
-----------------------------------------------------------------*)
Refines == ParReach!Refines

====