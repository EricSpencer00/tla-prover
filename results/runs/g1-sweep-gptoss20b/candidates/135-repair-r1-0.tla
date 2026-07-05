---- MODULE MCReachable ----
EXTENDS Reachable

ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes]
  : \A n \in Nodes : Cardinality(succ[n]) = 2

LimitedSeq == CHOOSE len \in 1 .. Cardinality(Nodes) :
  CHOOSE f \in [1 .. len -> Nodes] : TRUE

============================