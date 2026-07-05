---- MODULE MCDistributedReplicatedLog ----
EXTENDS DistributedReplicatedLog, FiniteSetsExt

ASSUME
    \* LongestCommonPrefix in View for a single server would always shorten the
    \* log to <<>>, reducing the state-space to a single state.
    Cardinality(Servers) > 1

ASSUME IsFiniteSet(Values)

\* View that replaces the original DropCommonPrefix.
\* The identity mapping is used so that the semantics of the system are
\* unchanged and the temporal property InSync can be verified.
DropCommonPrefix == cLogs

====