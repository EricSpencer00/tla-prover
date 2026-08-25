---- MODULE MCParReach ----
EXTENDS ParReach, Sequences

\*----------------------------------------------------------------------
\* Constants required by the configuration (already declared in the
\* underlying modules, but kept here for clarity)
\*----------------------------------------------------------------------
CONSTANT Nodes, Root, Procs

\*----------------------------------------------------------------------
\* Succ operator – overridden by the .cfg file with ConnectedToSomeButNotAll
\* (no local definition; the .cfg will replace Succ with the operator
\* defined below)
\*----------------------------------------------------------------------
\* Operator that will replace Succ in the .cfg file.
\* For each node it nondeterministically chooses a set of exactly two
\* distinct successors (different from the node itself). The choice is
\* made once for the whole model, so the graph is fixed during a run.
\*----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  CHOOSE S \in SUBSET Nodes :
        Cardinality(S) = 2 /\ n \notin S

\*----------------------------------------------------------------------
\* Finite‑sequence operator that replaces Seq (from the Sequences module)
\* with a version whose length is bounded by the number of nodes.
\*----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

====