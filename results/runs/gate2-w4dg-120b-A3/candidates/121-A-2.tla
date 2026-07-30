---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet

ZSequences == [ZSequences]CharacterSet

MaxStringLength == 2

StringIndices(s) == 0 .. (Len(s) - 1)

Sentinel == 99

VARIABLES inputString, stringLength, failFunc, patIndex, loopCount, bestOffset, pc

vars == <<inputString, stringLength, failFunc, patIndex, loopCount, bestOffset, pc>>

Init ==
    /\ inputString \in [1 .. MaxStringLength -> ZSequences]
    /\ stringLength = Len(inputString)
    /\ failFunc = [i \in 0 .. (2 * MaxStringLength) |-> Sentinel]
    /\ patIndex = Sentinel
    /\ loopCount = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

LookupFailure ==
    /\ failFunc' = [failFunc EXCEPT ![loopCount - 1 - bestOffset] = failFunc[loopCount - 1 - bestOffset]]
    /\ pc' = "innerComp"
    /\ UNCHANGED <<inputString, stringLength, patIndex, loopCount, bestOffset>>

InnerComp ==
    /\ IF loopCount % stringLength = (bestOffset + (IF patIndex = Sentinel THEN 0 ELSE patIndex + 1)) % stringLength
       THEN pc' = "postComp"
       ELSE pc' = "followFailure"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patIndex, loopCount, bestOffset>>

FollowFailure ==
    /\ patIndex' = failFunc[loopCount - 1 - bestOffset]
    /\ pc' = "innerComp"
    /\ UNCHANGED <<inputString, stringLength, failFunc, loopCount, bestOffset>>

UpdateOnLess ==
    /\ inputString[(loopCount - 1) % stringLength + 1] < inputString[(bestOffset + (IF patIndex = Sentinel THEN 0 ELSE patIndex + 1)) % stringLength + 1]
    /\ bestOffset' = loopCount - 1
    /\ UNCHANGED <<inputString, stringLength, failFunc, patIndex, loopCount, pc>>

PostComp ==
    /\ IF loopCount % stringLength # (bestOffset + (IF patIndex = Sentinel THEN 0 ELSE patIndex + 1)) % stringLength /\ patIndex = Sentinel
       THEN UpdateOnLess
       ELSE UNCHANGED <<bestOffset>>
    /\ failFunc' = [failFunc EXCEPT ![loopCount - 1 - bestOffset] = IF patIndex = Sentinel THEN Sentinel ELSE patIndex + 1]
    /\ patIndex' = Sentinel
    /\ pc' = "increment"

Increment ==
    /\ loopCount' = loopCount + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patIndex, bestOffset>>

Terminate ==
    /\ pc = "outerCheck"
    /\ loopCount >= 2 * MaxStringLength
    /\ pc' = "terminated"
    /\ UNCHANGED <<inputString, stringLength, failFunc, patIndex, loopCount, bestOffset>>

Idle ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next ==
    \/ LookupFailure
    \/ InnerComp
    \/ FollowFailure
    \/ UpdateOnLess
    \/ PostComp
    \/ Increment
    \/ Terminate
    \/ Idle

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

TypeInvariant ==
    /\ inputString \in [1 .. MaxStringLength -> ZSequences]
    /\ stringLength = Len(inputString)
    /\ failFunc \in [0 .. (2 * MaxStringLength) -> 0 .. (2 * MaxStringLength) \cup {Sentinel}]
    /\ patIndex \in 0 .. (2 * MaxStringLength) \cup {Sentinel}
    /\ loopCount \in 0 .. (2 * MaxStringLength)
    /\ bestOffset \in 0 .. MaxStringLength

RotationAt(i) == inputString[(i + 1) .. stringLength] \o inputString[1 .. i]

Correctness ==
    /\ \A i \in 0 .. (stringLength - 1) : RotationAt(bestOffset) <= RotationAt(i)
    /\ \A i \in 0 .. (stringLength - 1) : (RotationAt(i) = RotationAt(bestOffset)) => (i >= bestOffset)

Termination ==
    <>(pc = "terminated")

====