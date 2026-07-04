---- MODULE MCReachable ----
EXTENDS Reachable, Sequences

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq(S) ==
  { seq \in Seq(S) : Len(seq) \in 0 .. Cardinality(Nodes) }

====