---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

CONSTANTS
    CharacterSet

Variables
    inputString
    stringLength
    failureFunc
    patternIndex
    loopCounter
    bestOffset
    pc

vars == <<inputString, stringLength, failureFunc, patternIndex, loopCounter, bestOffset, pc>>

AllSeqs == UNION { [1..n -> CharacterSet] : n \in (Nat \ {0}) }

Sentinel == 0 - 1

TypeInvariant ==
    /\ inputString \in AllSeqs
    /\ stringLength = Len(inputString)
    /\ failureFunc \in [0..(2 * stringLength) -> (-1)..stringLength]
    /\ patternIndex \in ((-1)..stringLength)
    /\ loopCounter \in 1..(2 * stringLength + 1)
    /\ bestOffset \in 0..(stringLength - 1)
    /\ pc \in {"outerCheck", "failureLookup", "innerLoop", "updateBest", "followFail", "postCompare", "increment", "terminated"}

Init ==
    /\ inputString \in AllSeqs
    /\ stringLength = Len(inputString)
    /\ failureFunc = [i \in 0..(2 * stringLength) |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCounter < 2 * stringLength
         THEN /\ pc' = "failureLookup"
              /\ UNCHANGED <<inputString, stringLength, failureFunc, patternIndex, loopCounter, bestOffset>>
         ELSE /\ pc' = "terminated"
              /\ UNCHANGED <<inputString, stringLength, failureFunc, patternIndex, loopCounter, bestOffset>>

FailureLookup ==
    /\ pc = "failureLookup"
    /\ patternIndex' = failureFunc[loopCounter - bestOffset]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<inputString, stringLength, failureFunc, loopCounter, bestOffset>>

InnerLoop ==
    /\ pc = "innerLoop"
    /\ LET curChar == inputString[((loopCounter - 1) % stringLength) + 1]
           candChar == inputString[((bestOffset + patternIndex) % stringLength) + 1]
       IN (curChar # candChar /\ patternIndex # Sentinel)
    /\ pc' = "followFail"
    /\ UNCHANGED <<inputString, stringLength, failureFunc, patternIndex, loopCounter, bestOffset>>

UpdateBest ==
    /\ pc = "innerLoop"
    /\ LET curChar == inputString[((loopCounter - 1) % stringLength) + 1]
           candChar == inputString[((bestOffset + patternIndex) % stringLength) + 1]
       IN (curChar < candChar)
    /\ bestOffset' = loopCounter - 1
    /\ pc' = "followFail"
    /\ UNCHANGED <<inputString, stringLength, failureFunc, patternIndex, loopCounter>>

FollowFail ==
    /\ pc = "followFail"
    /\ patternIndex' = failureFunc[patternIndex]
    /\ pc' = "postCompare"
    /\ UNCHANGED <<inputString, stringLength, failureFunc, loopCounter, bestOffset>>

PostCompare ==
    /\ pc = "postCompare"
    /\ LET curChar == inputString[((loopCounter - 1) % stringLength) + 1]
           candChar == inputString[((bestOffset + patternIndex) % stringLength) + 1]
           newBest == IF curChar < candChar THEN loopCounter - 1 ELSE bestOffset
           newFunc == IF patternIndex = Sentinel THEN Sentinel ELSE patternIndex + 1
       IN \E b \in (0..(stringLength - 1)) :
              /\ b \in {newBest}
              /\ failureFunc' = [failureFunc EXCEPT ![loopCounter - bestOffset] = newFunc]
    /\ bestOffset' = newBest
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, stringLength, patternIndex, loopCounter>>

Increment ==
    /\ pc = "increment"
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, stringLength, failureFunc, patternIndex, bestOffset>>

Stall ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ FailureLookup
    \/ InnerLoop
    \/ UpdateBest
    \/ FollowFail
    \/ PostCompare
    \/ Increment
    \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup) /\ WF_vars(Increment)

Correctness ==
    /\ \A shift \in 0..(stringLength - 1) :
         inputString[[1..stringLength] +-> [j \in 0..(stringLength - 1) |-> inputString[((j + shift) % stringLength) + 1]]]
         <= inputString[[1..stringLength] +-> [j \in 0..(stringLength - 1) |-> inputString[((j + bestOffset) % stringLength) + 1]]]
    /\ \A shift \in 0..(stringLength - 1) :
         (inputString[[1..stringLength] +-> [j \in 0..(stringLength - 1) |-> inputString[((j + shift) % stringLength) + 1]]]
          = inputString[[1..stringLength] +-> [j \in 0..(stringLength - 1) |-> inputString[((j + bestOffset) % stringLength) + 1]]])
         => shift >= bestOffset

Termination == <>(pc = "terminated")
====