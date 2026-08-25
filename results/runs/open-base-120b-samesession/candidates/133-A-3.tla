---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES Marked, Frontier, pc, sel, succ

(*--------------------------------------------------------------------
   Include the parallel reachability algorithm specification.
   The parallel algorithm is assumed to be defined in the module
   ParReach and to use the same identifiers for its constants and
   variables.
--------------------------------------------------------------------*)
INSTANCE ParReach WITH
    Nodes   <- Nodes,
    Root    <- Root,
    Procs   <- Procs,
    Succ    <- Succ,
    Marked  <- Marked,
    Frontier<- Frontier,
    pc      <- pc,
    sel     <- sel,
    succ    <- succ

(*--------------------------------------------------------------------
   Initial state and next-state relation are taken directly from the
   parallel algorithm.
--------------------------------------------------------------------*)
Init == ParReach!Init
Next == ParReach!Next

(*--------------------------------------------------------------------
   Specification required by the .cfg file.
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc, sel, succ>>

(*--------------------------------------------------------------------
   Invariant and refinement property required by the .cfg file.
--------------------------------------------------------------------*)
Inv == ParReach!Inv
Refines == ParReach!Refines

(*--------------------------------------------------------------------
   Concrete graph: 4 nodes, each node has exactly 2 successors.
--------------------------------------------------------------------*)
Edge == {
    <<1, 2>>, <<1, 3>>,
    <<2, 3>>, <<2, 4>>,
    <<3, 1>>, <<3, 4>>,
    <<4, 1>>, <<4, 2>>
}

(*--------------------------------------------------------------------
   Bounded successor function that will replace the generic Succ
   operator in the configuration.  For any node n, it returns the set
   of its two successors according to the Edge relation.
--------------------------------------------------------------------*)
ConnectedToSomeButNotAll(n) ==
    IF n \in Nodes THEN
        { s \in Nodes : <<n, s>> \in Edge }
    ELSE {}

(*--------------------------------------------------------------------
   Bounded sequence operator that replaces Seq from the Sequences
   module.  Sequences are limited to length at most |Nodes|.
--------------------------------------------------------------------*)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====