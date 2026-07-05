---- MODULE MCDistributedReplicatedLog ----
EXTENDS DistributedReplicatedLog, FiniteSetsExt

ASSUME
    \* LongestCommonPrefix in View for a single server would always shorten the
    \* log to <<>>, reducing the state-space to a single state.
    Cardinality(Servers) > 1

    \* Combining the following conditions makes the state space finite:
    \* 1) The divergence of any two logs is bounded (See Extend action)
    \*
    \* 2) Terms is a *finite* set.
    IsFiniteSet(Values)

    \* Require that after dropping the longest common prefix, all servers
    \* observe the same remaining log fragment.  This ensures that the
    \* InSync property is non‑vacuously satisfied.
    \A s, t \in Servers : DropCommonPrefix[s] = DropCommonPrefix[t]

\* The longest common prefix of all logs is discarded.
DropCommonPrefix ==
    LET commonPrefixBound == Len(LongestCommonPrefix(Range(cLogs)))
        Drop(seq, idx) == SubSeq(seq, idx + 1, Len(seq))
    IN [ s \in Servers |-> Drop(cLogs[s], commonPrefixBound) ]

====