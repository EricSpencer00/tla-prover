---- MODULE MCReachable ----
EXTENDS Reachable

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq ==
  UNION {
    [1 .. len -> Nodes] :
      len \in 0 .. Cardinality(Nodes)
  }
====