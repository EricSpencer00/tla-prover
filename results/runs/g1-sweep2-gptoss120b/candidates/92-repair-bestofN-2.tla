---- MODULE MCDistributedReplicatedLog ----
EXTENDS DistributedReplicatedLog, FiniteSetsExt

ASSUME
    \* LongestCommonPrefix in View for a single server would always shorten the
    \* log to <<>>, reducing the state-space to a single state.
    Cardinality(Servers) > 1

====