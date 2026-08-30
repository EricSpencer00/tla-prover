---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

CONSTANTS CharacterSet

VARIABLES inputString, strLen, failureFunc, patternIndex, loopCounter, bestOffset, pc

vars == <<inputString, strLen, failureFunc, patternIndex, loopCounter, bestOffset, pc>>

Sentinel == 255
MaxLen == 2
MaxChar == 1
Corpus == [k \in 0..(2^MaxLen - 1) |-> IF k = 0 THEN <<>> ELSE LET a == k % (MaxChar + 1) IN <<a>>]

TypeInvariant ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ failureFunc \in [0..(2 * strLen) -> (0..(2 * strLen) \cup {Sentinel})]
  /\ patternIndex \in (0..(2 * strLen)) \cup {Sentinel}
  /\ loopCounter \in 0..(2 * strLen)
  /\ bestOffset \in 0..(strLen - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateOffset", "followChain", "postComparison", "increment", "done"}

Init ==
  /\ \E s \in Corpus : inputString = s
  /\ strLen = Len(inputString)
  /\ failureFunc = [i \in 0..(2 * strLen) |-> Sentinel]
  /\ patternIndex = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCounter < 2 * strLen THEN pc' = "lookup" ELSE pc' = "done"
  /\ UNCHANGED <<inputString, strLen, failureFunc, patternIndex, loopCounter, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ failureFunc' = [failureFunc EXCEPT ![loopCounter % strLen] = failureFunc[loopCounter % strLen]]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, strLen, patternIndex, loopCounter, bestOffset>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ IF loopCounter % strLen # bestOffset + patternIndex % strLen
       THEN pc' = IF patternIndex = Sentinel THEN "postComparison" ELSE "innerLoop"
       ELSE pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, failureFunc, patternIndex, loopCounter, bestOffset>>

UpdateOffset ==
  /\ pc = "updateOffset"
  /\ inputString[loopCounter % strLen] < inputString[(bestOffset + patternIndex) % strLen]
  /\ bestOffset' = loopCounter % strLen
  /\ pc' = "followChain"
  /\ UNCHANGED <<inputString, strLen, failureFunc, patternIndex, loopCounter>>

FollowChain ==
  /\ pc = "followChain"
  /\ patternIndex' = failureFunc[patternIndex]
  /\ pc' = "postComparison"
  /\ UNCHANGED <<inputString, strLen, failureFunc, loopCounter, bestOffset>>

PostComparison ==
  /\ pc = "postComparison"
  /\ IF loopCounter % strLen # bestOffset + patternIndex % strLen /\ patternIndex = Sentinel
       THEN bestOffset' = IF inputString[loopCounter % strLen] < inputString[(bestOffset + patternIndex) % strLen]
                            THEN loopCounter % strLen ELSE bestOffset
       ELSE bestOffset' = bestOffset
  /\ failureFunc' = [failureFunc EXCEPT ![loopCounter % strLen] =
                       IF patternIndex = Sentinel THEN 0 ELSE patternIndex + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, patternIndex, loopCounter>>

Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, strLen, failureFunc, patternIndex, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == OuterCheck \/ Lookup \/ InnerLoop \/ UpdateOffset \/ FollowChain \/ PostComparison \/ Increment \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup) /\ WF_vars(InnerLoop)
  /\ WF_vars(UpdateOffset) /\ WF_vars(FollowChain) /\ WF_vars(PostComparison) /\ WF_vars(Increment)

Rotations == { inputString[(bestOffset + k) % strLen] : k \in 0..(strLen - 1) }

Correctness ==
  /\ bestOffset \in 0..(strLen - 1)
  /\ \A k \in 0..(strLen - 1) : inputString[(bestOffset + k) % strLen] \in Rotations
  /\ \A k \in 0..(strLen - 1) :
       (\A j \in 0..(strLen - 1) : inputString[(bestOffset + j) % strLen] <= inputString[(k + j) % strLen])
         => bestOffset <= k

Termination == <>(pc = "done")

====