---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, TLC, ParReach

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Procs, Succ

\* Concrete definition of the graph (4 nodes, each with exactly 2 successors)
ASSUME /\ Nodes = {"n0", "n1", "n2", "n3"}
       /\ Root \in Nodes
       /\ Procs = {"p0", "p1"}
       /\ Succ = [ n \in Nodes |-> 
                     CASE n = "n0" -> {"n1", "n2"} 
                      [] n = "n1" -> {"n2", "n3"} 
                      [] n = "n2" -> {"n3", "n0"} 
                      [] n = "n3" -> {"n0", "n1"} ]
       /\ \A n \in Nodes: Cardinality(Succ[n]) = 2

\* ----------------------------------------------------------------------
\* Operator that replaces the generic successor relation used in the
\* parallel algorithm.  It is simply the concrete graph defined above.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Bounded version of Seq (finite sequences of length at most |Nodes|)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Specification, invariants and properties required by the .cfg file.
\* They are delegated to the parallel reachability algorithm module.
\* ----------------------------------------------------------------------
Spec == ParReach!Spec
Inv  == ParReach!Inv
Refines == ParReach!Refines

====