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
        { m \in Nodes : 
            /\ m # n
            /\ \E q \in Nodes : (q # n) /\ (q # m)   \* placeholder to guarantee at least two
        }
    ]

(*-----------------------------------------------------------------
  Finite version of the generic sequence operator from the
  Sequences module.  The .cfg replaces Seq with LimitedSeq.
-----------------------------------------------------------------*)
LimitedSeq(S) == 
    { s : \E n \in 0..Cardinality(Nodes) : s \in [1..n -> S] }

====