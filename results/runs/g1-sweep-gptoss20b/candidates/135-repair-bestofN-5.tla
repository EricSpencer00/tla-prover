---- MODULE MCReachable ----
EXTENDS Reachable, Sequences

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes]
    : \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq(S) == { f \in Seq(S) : Len(f) <= Cardinality(Nodes) }

====