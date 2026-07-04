---- MODULE MCDistributedReplicatedLog ----
EXTENDS DistributedReplicatedLog, FiniteSetsExt

ASSUME
    \* LongestCommonPrefix in View for a single server would always shorten the
    \* log to <<>>, reducing the state-space to a single state.
    Cardinality(Servers) > 1

ASSUME IsFiniteSet(Values)

\* The view is kept minimal to preserve the semantics while avoiding accidental
\* state-space reduction that may hide counter‑examples.  The drop of the
\* common prefix is performed in the view used by the verification criteria.
DropCommonPrefix == cLogs

====