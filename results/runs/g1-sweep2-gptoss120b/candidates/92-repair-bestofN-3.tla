---- MODULE MCDistributedReplicatedLog ----
EXTENDS DistributedReplicatedLog, FiniteSetsExt

(*--------------------------------------------------------------------
  Assumptions
--------------------------------------------------------------------*)
ASSUME
    (* LongestCommonPrefix in View for a single server would always
       shorten the log to <<>>, reducing the state-space to a single state. *)
    Cardinality(Servers) > 1

(* Combining the following conditions makes the state space finite:
   1) The divergence of any two logs is bounded (see Extend action)
   2) Terms is a *finite* set.
   3) The longest common prefix of all logs is discarded. *)
ASSUME IsFiniteSet(Values)

(*--------------------------------------------------------------------
  VIEW definition
--------------------------------------------------------------------*)
DropCommonPrefix ==
    LET commonPrefixBound == Len(LongestCommonPrefix(Range(cLogs))) IN
        [ s \in Servers |-> 
            LET seq == cLogs[s] IN
                IF commonPrefixBound # Len(seq) THEN
                    SubSeq(seq, commonPrefixBound + 1, Len(seq))
                ELSE
                    <<>> ]

====