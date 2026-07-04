---- MODULE MCDistributedReplicatedLog ----
EXTENDS DistributedReplicatedLog, FiniteSetsExt

(***************************************************************************)
(* Assumptions                                                            *)
(***************************************************************************)

\* LongestCommonPrefix in View for a single server would always shorten the
\* log to <<>>, reducing the state-space to a single state.
ASSUME Cardinality(Servers) > 1

\* Combining the following conditions makes the state space finite:
\* 1) The divergence of any two logs is bounded (See Extend action)
\* 2) Terms is a *finite* set.
ASSUME IsFiniteSet(Values)

\* 3) The longest common prefix of all logs is discarded.
\*    The view DropCommonPrefix is used by the model checker to prune the
\*    state space while preserving the semantics required by the invariants
\*    and properties of the system.
(***************************************************************************)

\* Helper that returns the suffix of a sequence after removing the first
\* `n` elements.  If `n` is greater than or equal to the length of the
\* sequence, the result is the empty sequence <<>>.
Suffix(seq, n) ==
    IF n >= Len(seq) THEN <<>>
    ELSE SubSeq(seq, n + 1, Len(seq))

\* The view used by TLC.  It drops the longest common prefix shared by all
\* server logs.  The definition is written so that it is total and
\* deterministic for every reachable state.
DropCommonPrefix ==
    LET commonPrefix == LongestCommonPrefix(Range(cLogs))
        commonPrefixBound == Len(commonPrefix)
    IN [ s \in Servers |-> Suffix(cLogs[s], commonPrefixBound) ]

(***************************************************************************)
(*  Specification with fairness                                            *)
(***************************************************************************)

\* We inherit the base specification from DistributedReplicatedLog and
\* strengthen it with weak fairness for the Copy action.  This prevents
\* unfair behaviors (such as the looping counter‑example) that violate
\* the temporal property InSync while preserving the original semantics.
Spec == DistributedReplicatedLog!Spec /\ WF_vars(Copy)

====