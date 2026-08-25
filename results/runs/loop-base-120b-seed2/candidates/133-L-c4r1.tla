---- MODULE MCParReach ----
EXTENDS ParReach, Sequences

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

====