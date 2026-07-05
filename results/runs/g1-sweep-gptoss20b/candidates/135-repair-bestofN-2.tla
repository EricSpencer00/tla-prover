---- MODULE MCReachable ----
EXTENDS Reachable

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes]
  : \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq(S) ==
  CHOOSE seq \in [1 .. Cardinality(Nodes) -> S] : TRUE

====