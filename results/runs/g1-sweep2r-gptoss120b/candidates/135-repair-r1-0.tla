---- MODULE MCReachable ----
EXTENDS Reachable, Sequences

(* Each node is connected to a non‑empty proper subset of the nodes.
   This satisfies the “some but not all” intent while preserving the
   original requirement that every node have at least one successor
   and not be connected to every node. *)
ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes :
      Cardinality(succ[n]) \in 1 .. (Cardinality(Nodes) - 1)

(* Returns the set of all sequences over S whose length does not exceed
   the number of nodes.  This uses the standard Seq and Len operators
   from the Sequences module, preserving the intended semantics of the
   original definition. *)
LimitedSeq(S) ==
  { seq \in Seq(S) : Len(seq) \in 0 .. Cardinality(Nodes) }

====