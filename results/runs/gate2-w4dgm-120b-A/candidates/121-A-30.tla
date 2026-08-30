---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT CharacterSet

\* The linear-time lexicographically-least circular substring algorithm from
\* Booth's 1980 paper.  The input string is chosen nondeterministically
\* from all sequences over a finite character set (the corpus); the spec
\* checks the result for every such string up to the configured length.
\* The failure function is the KMP-style table that lets the algorithm
\* skip past character runs it has already resolved.

\* The model checker bounds the character set size and the max string
\* length via a separate .cfg file; here they are left symbolic so the
\* spec is valid for any configuration the user chooses within that bound.

\* All sequence indexing is zero-based, matching the paper's description
\* (the standard TLA+ Sequences module is one-indexed), so the code is
\* written to count from 0 throughout.

Sentinel == 99

VARIABLES seq, seqLen, ffunc, matchIdx, loopPos, bestOffset, pc

vars == <<seq, seqLen, ffunc, matchIdx, loopPos, bestOffset, pc>>

TypeInvariant ==
  /\ seq \in CharacterSet
  /\ seqLen = Len(seq)
  /\ ffunc \in [0..(seqLen * 2) -> 0..(seqLen * 2) \cup {Sentinel}]
  /\ matchIdx \in 0..(seqLen * 2) \cup {Sentinel}
  /\ loopPos \in 1..(seqLen * 2) \cup {Sentinel}
  /\ bestOffset \in 0..(seqLen - 1)
  /\ pc \in {"outerCheck", "failureLookup", "innerLoop",
             "updateOnLess", "followChain", "postComparison",
             "increment", "done"}

Init ==
  /\ \E s \in CharacterSet : seq = s
  /\ seqLen = Len(seq)
  /\ ffunc = [i \in 0..(seqLen * 2) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loopPos = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopPos < (seqLen * 2)
     THEN pc' = "failureLookup"
     ELSE pc' = "done"
  /\ UNCHANGED <<seq, seqLen, ffunc, matchIdx, loopPos, bestOffset>>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ matchIdx' = ffunc[loopPos - 1]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<seq, seqLen, ffunc, loopPos, bestOffset>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ seq[(loopPos % seqLen)] # seq[(loopPos + bestOffset) % seqLen]
  /\ matchIdx # Sentinel
  /\ pc' = "followChain"
  /\ UNCHANGED <<seq, seqLen, ffunc, matchIdx, loopPos, bestOffset>>

UpdateOnLess ==
  /\ pc = "innerLoop"
  /\ seq[(loopPos % seqLen)] < seq[(loopPos + bestOffset) % seqLen]
  /\ bestOffset' = loopPos
  /\ pc' = "updateOnLess"
  /\ UNCHANGED <<seq, seqLen, ffunc, matchIdx, loopPos>>

FollowChain ==
  /\ pc = "followChain"
  /\ matchIdx' = ffunc[matchIdx]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<seq, seqLen, ffunc, loopPos, bestOffset>>

PostComparison ==
  /\ pc = "innerLoop"
  /\ seq[(loopPos % seqLen)] # seq[(loopPos + bestOffset) % seqLen]
  /\ matchIdx = Sentinel
  /\ (IF seq[(loopPos % seqLen)] < seq[(loopPos + bestOffset) % seqLen]
        THEN bestOffset' = loopPos ELSE bestOffset' = bestOffset)
  /\ ffunc' = [ffunc EXCEPT ![loopPos] = IF matchIdx = Sentinel
                                       THEN Sentinel ELSE matchIdx + 1]
  /\ pc' = "postComparison"
  /\ UNCHANGED <<seq, seqLen, matchIdx, loopPos>>

Increment ==
  /\ pc \in {"postComparison", "updateOnLess"}
  /\ loopPos' = loopPos + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<seq, seqLen, ffunc, matchIdx, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ FailureLookup \/ InnerLoop \/ UpdateOnLess
  \/ FollowChain \/ PostComparison \/ Increment \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Increment)

Correctness ==
  /\ (seqLen > 0 => bestOffset \in 0..(seqLen - 1))
  /\ \A i \in 0..(seqLen - 1) :
        Rotate(seq, bestOffset) <= Rotate(seq, i)
  /\ \A i \in 0..(seqLen - 1) :
        Rotate(seq, bestOffset) = Rotate(seq, i) => bestOffset <= i

Rotate(sq, off) == SubSeq(sq, off, seqLen - off) \o SubSeq(sq, 0, off)

Termination == <>(pc = "done")

====