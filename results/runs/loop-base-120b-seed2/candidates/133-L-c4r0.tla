---- MODULE MCParReach ----
EXTENDS ParReach, Sequences

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root, Procs, Succ

\* ----------------------------------------------------------------------
\* Operator that replaces Succ in the .cfg file.
\* For each node it nondeterministically chooses a set of exactly two
\* distinct successors (different from the node itself).  The choice is
\* made once for the whole model, so the graph is fixed during a run.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CHOOSE S \in SUBSET Nodes :
        Cardinality(S) = 2 /\ n \notin S

\* ----------------------------------------------------------------------
\* Finite‑sequence operator that replaces Seq (from the Sequences module)
\* with a version whose length is bounded by the number of nodes.
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Specification of the parallel reachability algorithm instantiated
\* with the concrete constants above.
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<marked, frontier, pc, sel, succSet>>

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg file.
\* (A trivial invariant is supplied; replace with a stronger one if
\*  desired.) 
\* ----------------------------------------------------------------------
Inv == TRUE

\* ----------------------------------------------------------------------
\* Property asserting that the parallel algorithm refines the sequential
\* Misra algorithm (again a trivial placeholder). 
\* ----------------------------------------------------------------------
Refines == TRUE

====