---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Indexing is zero-based here, not one-based as in the standard module. The
\* sentinel value is one past the largest valid index into the failure array.
Sentinel == 6

VARIABLES inputString, length, failure, patternIndex, loopCnt, bestOffset, pc

vars == <<inputString, length, failure, patternIndex, loopCnt, bestOffset, pc>>

\* The corpus: all zero-indexed sequences over the character set, up to length 5.
Corpus == {s \in Seq(CharacterSet) : Len(s) <= 5}

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure \in [0..(2 * length) -> 0..Sentinel]
  /\ patternIndex \in 0..Sentinel
  /\ loopCnt \in 0..(2 * length)
  /\ bestOffset \in 0..(length - 1)

\* A lexicographically-minimal rotation is smaller than every other rotation.
LexicographicallyMinimal ==
  /\ \A i \in 0..(length - 1) : SubSeq(inputString, bestOffset, length - 1) ^ SubSeq(inputString, 0, bestOffset - 1) <= SubSeq(inputString, i, length - 1) ^ SubSeq(inputString, 0, i - 1)
  /\ \A i \in 0..(length - 1) : SubSeq(inputString, bestOffset, length - 1) ^ SubSeq(inputString, 0, bestOffset - 1) = SubSeq(inputString, i, length - 1) ^ SubSeq(inputString, 0, i - 1) => i >= bestOffset

Init ==
  \E s \in Corpus :
    /\ inputString = s
    /\ length = Len(s)
    /\ failure = [k \in 0..10 |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ loopCnt = 1
    /\ bestOffset = 0
    /\ pc = "OuterCheck"

OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF loopCnt < (2 * length)
       THEN pc' = "Lookup"
       ELSE pc' = "Done"
  /\ UNCHANGED <<inputString, length, failure, patternIndex, loopCnt, bestOffset>>

Lookup ==
  /\ pc = "Lookup"
  /\ failure' = [failure EXCEPT ![loopCnt] = failure[bestOffset + loopCnt]]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<inputString, length, patternIndex, loopCnt, bestOffset>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ LET cur == inputString[(loopCnt % length) + 1] IN
     LET cand == inputString[((bestOffset + loopCnt) % length) + 1] IN
       IF cur = cand /\ patternIndex # Sentinel
         THEN patternIndex' = failure[patternIndex]
         ELSE pc' = "PostCompare"
  /\ UNCHANGED <<inputString, length, failure, loopCnt, bestOffset>>

LessThanCandidate ==
  /\ pc \in {"InnerLoop", "PostCompare"}
  /\ inputString[(loopCnt % length) + 1] < inputString[((bestOffset + loopCnt) % length) + 1]
  /\ bestOffset' = loopCnt
  /\ UNCHANGED <<inputString, length, failure, patternIndex, loopCnt, pc>>

FailureChain ==
  /\ pc = "InnerLoop"
  /\ patternIndex' = failure[patternIndex]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<inputString, length, failure, loopCnt, bestOffset>>

PostCompare ==
  /\ pc = "PostCompare"
  /\ LET cur == inputString[(loopCnt % length) + 1] IN
     LET cand == inputString[((bestOffset + loopCnt) % length) + 1] IN
       IF cur # cand /\ patternIndex = Sentinel
         THEN IF cur < cand
               THEN bestOffset' = loopCnt
               ELSE bestOffset' = bestOffset
         ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![bestOffset + loopCnt] = IF inputString[(loopCnt % length) + 1] = inputString[((bestOffset + loopCnt) % length) + 1] THEN patternIndex ELSE patternIndex + 1]
  /\ pc' = "Increment"
  /\ UNCHANGED <<inputString, length, patternIndex, loopCnt>>

Increment ==
  /\ pc = "Increment"
  /\ loopCnt' = loopCnt + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<inputString, length, failure, patternIndex, bestOffset>>

\* Once terminated, the algorithm may idle.
Stall ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ InnerLoop \/ FailureChain \/ PostCompare \/ Increment \/ Stall
  \/ LessThanCandidate

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ SF_vars(LessThanCandidate)

Termination == <>(pc = "Done")

====