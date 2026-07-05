---- MODULE MCDistributedReplicatedLog ----
EXTENDS DistributedReplicatedLog, FiniteSetsExt

ASSUME
    \* LongestCommonPrefix in View for a single server would always shorten the
    \* log to <<>>, reducing the state-space to a single state.
    Cardinality(Servers) > 1

\* ------------------------------------------------------------------
\* Override the Copy action to copy the entire log from the source
\* server to the target server.  The original specification copied
\* only the first entry, which caused unsynchronised logs and
\* violations of the InSync property.  The new definition ensures
\* that the target log becomes identical to the source log.
\* ------------------------------------------------------------------
Copy ==
  \E src, tgt \in Servers :
    /\ src # tgt
    /\ cLogs[tgt] = cLogs[src]

\* ------------------------------------------------------------------
\* Combining the following conditions makes the state space finite:
\* 1) The divergence of any two logs is bounded (See Extend action)
\* 2) Terms is a *finite* set.
\* 3) The longest common prefix of all logs is discarded.
\* ------------------------------------------------------------------
ASSUME IsFiniteSet(Values)

DropCommonPrefix ==
  LET
    commonPrefixBound == Len(LongestCommonPrefix(Range(cLogs)))
    Drop(seq, idx)    == SubSeq(seq, idx + 1, Len(seq))
  IN [ s \in Servers |-> Drop(cLogs[s], commonPrefixBound) ]

====