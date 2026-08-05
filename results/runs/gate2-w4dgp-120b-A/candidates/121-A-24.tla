---- MODULE LeastCircularSubstring ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS CharacterSet

None == 99

VARIABLES inputString, length, failureFn, patternMatch, loopCounter, bestOffset, pc

vars == <<inputString, length, failureFn, patternMatch, loopCounter, bestOffset, pc>>

ZSequences == [a \in 0..(CharacterSet - 1)]

TypeInvariant ==
  /\ inputString \in SUBSET ZSequences
  /\ length = Len(inputString)
  /\ failureFn \in [0..(2 * length) -> {None} \union 0..(2 * length)]
  /\ patternMatch \in {None} \union (0..(2 * length))
  /\ loopCounter \in 0..(2 * length)
  /\ bestOffset \in 0..(If length = 0 Then 0 Else length - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "candidateBetter", "followChain", "postComparison", "increment", "terminated"}

Init ==
  /\ \E s \in SUBSET ZSequences : inputString = s
  /\ length = Len(inputString)
  /\ failureFn = [i \in 0..(2 * length) |-> None]
  /\ patternMatch = None
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

CandidateSeq(j) == inputString[(j % length) + 1]

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCounter < (2 * length)
       THEN pc' = "lookup"
       ELSE pc' = "terminated"
  /\ UNCHANGED <<inputString, length, failureFn, patternMatch, loopCounter, bestOffset>>

LookupFailureFn ==
  /\ pc = "lookup"
  /\ patternMatch' = failureFn[(loopCounter + bestOffset) % length]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, length, failureFn, loopCounter, bestOffset>>

InnerComparisonLoop ==
  /\ pc = "innerLoop"
  /\ IF CandidateSeq(loopCounter) # CandidateSeq(bestOffset + patternMatch)
       THEN IF patternMatch # None
              THEN pc' = "candidateBetter"
              ELSE pc' = "postComparison"
       ELSE pc' = "postComparison"
  /\ UNCHANGED <<inputString, length, failureFn, patternMatch, loopCounter, bestOffset>>

CandidateBetter ==
  /\ pc = "candidateBetter"
  /\ IF CandidateSeq(loopCounter) < CandidateSeq(bestOffset + patternMatch)
       THEN bestOffset' = loopCounter % length
       ELSE bestOffset' = bestOffset
  /\ pc' = "followChain"
  /\ UNCHANGED <<inputString, length, failureFn, patternMatch, loopCounter>>

FollowChain ==
  /\ pc = "followChain"
  /\ patternMatch' = failureFn[patternMatch]
  /\ pc' = "postComparison"
  /\ UNCHANGED <<inputString, length, failureFn, loopCounter, bestOffset>>

PostComparison ==
  /\ pc = "postComparison"
  /\ IF CandidateSeq(loopCounter) # CandidateSeq(bestOffset + patternMatch)
       THEN IF patternMatch = None
              THEN IF CandidateSeq(loopCounter) < CandidateSeq(bestOffset)
                     THEN bestOffset' = loopCounter % length
                     ELSE bestOffset' = bestOffset
                     /\ failureFn' = [failureFn EXCEPT ![loopCounter + bestOffset] = None]
              ELSE failureFn' = [failureFn EXCEPT ![loopCounter + bestOffset] = patternMatch + 1]
       ELSE bestOffset' = bestOffset
            /\ failureFn' = [failureFn EXCEPT ![loopCounter + bestOffset] = patternMatch + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, length, patternMatch, loopCounter>>

IncrementLoopCounter ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, length, failureFn, patternMatch, bestOffset>>

Stutter ==
  /\ pc = "terminated"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ LookupFailureFn \/ InnerComparisonLoop \/ CandidateBetter
  \/ FollowChain \/ PostComparison \/ IncrementLoopCounter \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(LookupFailureFn) /\ WF_vars(InnerComparisonLoop)
             /\ WF_vars(CandidateBetter) /\ WF_vars(FollowChain) /\ WF_vars(PostComparison)
             /\ WF_vars(IncrementLoopCounter)

Terminated == (pc = "terminated")

Correctness ==
  /\ (Terminated => \A i \in 0..(If length = 0 Then 0 Else length - 1) : CandidateSeq(bestOffset) <= CandidateSeq(i))
  /\ (Terminated
       => \A i \in 0..(If length = 0 Then 0 Else length - 1)
            : CandidateSeq(bestOffset) = CandidateSeq(i) => bestOffset <= i)

Termination == Terminated

====