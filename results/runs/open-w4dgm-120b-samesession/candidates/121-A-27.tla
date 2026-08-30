---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

CONSTANTS CharacterSet

\* Sequences are zero-indexed with length as a separate variable; indices are
\* checked against the length, and the i-th character is accessed as seq[i].
\* The action set is the full set of labeled steps of Booth's algorithm.

Sentinel == 255
MaxLen == 4
MaxChar == 2

VARIABLES seq, seqlen, fail, patIdx, loop, best, pc

vars == <<seq, seqlen, fail, patIdx, loop, best, pc>>

TypeInvariant ==
  /\ seq \in [0..(MaxLen - 1) -> CharacterSet]
  /\ seqlen \in 0..MaxLen
  /\ fail \in [0..(2 * MaxLen) -> (0..(2 * MaxLen)) \cup {Sentinel}]
  /\ patIdx \in (0..(2 * MaxLen)) \cup {Sentinel}
  /\ loop \in 1..(2 * MaxLen)
  /\ best \in 0..(MaxLen - 1)

\* The lexicographically-minimal rotation must be no greater than any other;
\* among equal rotations, the smallest offest (shift) must win.
\* Compare two rotations by walking the doubled string from each offset.
Correctness ==
  /\ \A j \in 0..(seqlen - 1) : \E k \in 0..seqlen : seq[(best + k) % seqlen] < seq[(j + k) % seqlen]
  /\ \A j \in 0..(seqlen - 1) :
       (\A k \in 0..seqlen : seq[(best + k) % seqlen] = seq[(j + k) % seqlen]) => best <= j

Init ==
  /\ \E s \in [0..(MaxLen - 1) -> CharacterSet] : seq = s
  /\ seqlen = Len(seq)
  /\ fail = [i \in 0..(2 * MaxLen) |-> Sentinel]
  /\ patIdx = Sentinel
  /\ loop = 1
  /\ best = 0
  /\ pc = "outer"

OuterIter ==
  /\ pc = "outer"
  /\ loop < (2 * seqlen)
  /\ pc' = "failureLookup"
  /\ UNCHANGED <<seq, seqlen, fail, patIdx, loop, best>>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ fail' = [fail EXCEPT ![loop - 1] = IF fail[loop - 1] # Sentinel THEN fail[loop - 1] ELSE Sentinel]
  /\ pc' = "compare"
  /\ UNCHANGED <<seq, seqlen, patIdx, loop, best>>

\* The inner loop walks the doubled string; the loop counter is the absolute
\* index, modulo the length for wrap-around.
Compare ==
  /\ pc = "compare"
  /\ seq[(loop % seqlen)] # seq[(best + loop) % seqlen]
  /\ patIdx # Sentinel
  /\ pc' = "compare"
  /\ UNCHANGED <<seq, seqlen, fail, patIdx, loop, best>>

UpdateBest ==
  /\ pc = "compare"
  /\ seq[(loop % seqlen)] < seq[(best + loop) % seqlen]
  /\ patIdx # Sentinel
  /\ best' = loop
  /\ pc' = "follow"
  /\ UNCHANGED <<seq, seqlen, fail, patIdx, loop>>

FollowFailure ==
  /\ pc = "compare"
  /\ patIdx' = fail[patIdx]
  /\ pc' = "postcompare"
  /\ UNCHANGED <<seq, seqlen, fail, loop, best>>

PostCompare ==
  /\ pc = "postcompare"
  /\ IF seq[(loop % seqlen)] # seq[(best + loop) % seqlen] /\ patIdx = Sentinel
       THEN IF seq[(loop % seqlen)] < seq[(best + loop) % seqlen]
              THEN best' = loop
              ELSE best' = best
            / fail' = [fail EXCEPT ![loop] = Sentinel]
       ELSE fail' = [fail EXCEPT ![loop] = IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<seq, seqlen, patIdx, loop>>

Increment ==
  /\ pc = "increment"
  /\ loop' = loop + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<seq, seqlen, fail, patIdx, best>>

Done ==
  /\ pc = "outer"
  /\ loop >= (2 * seqlen)
  /\ pc' = "done"
  /\ UNCHANGED <<seq, seqlen, fail, patIdx, loop, best>>

Stalling ==
  /\ pc = "done"
  /\ pc' = "done"
  /\ UNCHANGED <<seq, seqlen, fail, patIdx, loop, best>>

Next ==
  \/ OuterIter
  \/ FailureLookup
  \/ Compare
  \/ UpdateBest
  \/ FollowFailure
  \/ PostCompare
  \/ Increment
  \/ Done
  \/ Stalling

Spec == Init /\ [][Next]_vars
        /\ WF_vars(OuterIter) /\ WF_vars(FailureLookup) /\ WF_vars(Compare)
        /\ WF_vars(UpdateBest) /\ WF_vars(FollowFailure)
        /\ WF_vars(PostCompare) /\ WF_vars(Increment) /\ SF_vars(Done)

Termination == <>(pc = "done")
====