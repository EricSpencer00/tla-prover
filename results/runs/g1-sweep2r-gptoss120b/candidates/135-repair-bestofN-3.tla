---- MODULE MCReachable ----
EXTENDS Reachable

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) \in 0 .. Cardinality(Nodes) }

====