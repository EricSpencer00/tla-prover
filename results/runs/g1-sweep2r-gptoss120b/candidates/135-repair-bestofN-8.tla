---- MODULE MCReachable ----
EXTENDS Reachable

(* Choose a successor function that gives each node exactly two successors. *)
ConnectedToSomeButNotAll ==
  CHOOSE succ \in [Nodes -> SUBSET Nodes] :
    \A n \in Nodes : Cardinality(succ[n]) = 2

(* The set of all finite sequences (functions) of elements of S whose length
   does not exceed the number of nodes. *)
LimitedSeq(S) ==
  { f : \E len \in 0 .. Cardinality(Nodes) : f \in [1 .. len -> S] }

====