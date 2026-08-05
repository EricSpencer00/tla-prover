---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CharacterSet

VARIABLES inputString, inputLength, failFunc, patternIdx, loopCounter, bestOffset, pc

vars == <<inputString, inputLength, failFunc, patternIdx, loopCounter, bestOffset, pc>>

Unset == -1

Init == /\ inputString \in (CharacterSet)^+
        /\ inputLength = Len(inputString)
        /\ failFunc = [i \in 0..(2 * inputLength) |-> Unset]
        /\ patternIdx = Unset
        /\ loopCounter = 1
        /\ bestOffset = 0
        /\ pc = "outer"

OuterLoop == /\ loopCounter < (2 * inputLength)
             /\ pc' = "lookup"
             /\ UNCHANGED <<inputString, inputLength, failFunc, patternIdx, loopCounter, bestOffset>>

LookupFailure == /\ pc = "lookup"
                 /\ patternIdx' = failFunc[loopCounter - bestOffset]
                 /\ pc' = "compare"
                 /\ UNCHANGED <<inputString, inputLength, failFunc, loopCounter, bestOffset>>

CharAt(i) == inputString[(i % inputLength) + 1]

Compare == /\ pc = "compare"
           /\ (CharAt(loopCounter) # CharAt(patternIdx + 1) /\ patternIdx # Unset)
              => pc' = "compare"
           /\ (CharAt(loopCounter) # CharAt(patternIdx + 1) /\ patternIdx = Unset)
              => pc' = "postcompare"
           /\ (CharAt(loopCounter) = CharAt(patternIdx + 1))
              => pc' = "compare"
           /\ UNCHANGED <<inputString, inputLength, failFunc, patternIdx, loopCounter, bestOffset>>

RotateOnLess == /\ pc \in {"compare", "postcompare"}
                /\ CharAt(loopCounter) < CharAt(patternIdx + 1)
                /\ bestOffset' = loopCounter
                /\ UNCHANGED <<inputString, inputLength, failFunc, patternIdx, loopCounter, pc>>

FollowChain == /\ pc = "compare"
               /\ patternIdx # Unset
               /\ patternIdx' = failFunc[patternIdx]
               /\ UNCHANGED <<inputString, inputLength, failFunc, loopCounter, bestOffset, pc>>

PostCompare == /\ pc = "postcompare"
               /\ CharAt(loopCounter) < CharAt(patternIdx + 1)
               /\ bestOffset' = loopCounter
               /\ failFunc' = [failFunc EXCEPT ![loopCounter] = Unset]
               /\ UNCHANGED <<inputString, inputLength, patternIdx, loopCounter, pc>>

ResetFailure == /\ pc = "postcompare"
                /\ CharAt(loopCounter) >= CharAt(patternIdx + 1)
                /\ failFunc' = [failFunc EXCEPT ![loopCounter] = patternIdx + 1]
                /\ UNCHANGED <<inputString, inputLength, patternIdx, loopCounter, bestOffset, pc>>

Increment == /\ pc \in {"postcompare", "compare"}
             /\ loopCounter' = loopCounter + 1
             /\ pc' = "outer"
             /\ UNCHANGED <<inputString, inputLength, failFunc, patternIdx, bestOffset>>

Stall == /\ pc = "outer"
         /\ loopCounter >= (2 * inputLength)
         /\ UNCHANGED vars

Next == OuterLoop \/ LookupFailure \/ Compare \/ RotateOnLess \/ FollowChain
        \/ PostCompare \/ ResetFailure \/ Increment \/ Stall

TypeInvariant == /\ inputString \in (CharacterSet)^+
                 /\ inputLength = Len(inputString)
                 /\ failFunc \in [0..(2 * inputLength) -> (Unset..(2 * inputLength))]
                 /\ patternIdx \in (Unset..(2 * inputLength))
                 /\ loopCounter \in 0..(2 * inputLength)
                 /\ bestOffset \in 0..(inputLength - 1)
                 /\ pc \in {"outer", "lookup", "compare", "postcompare"}

LessOrEqual(i, j) == \A k \in 0..(inputLength - 1) : CharAt(i + k) <= CharAt(j + k)

Correctness == /\ (loopCounter >= (2 * inputLength) => pc = "outer")
                /\ \A j \in 0..(inputLength - 1) : LessOrEqual(bestOffset, j)
                /\ \A j \in 0..(inputLength - 1) : (LessOrEqual(bestOffset, j) /\ bestOffset > j)
                                        => CharAt(bestOffset) = CharAt(j)

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(LookupFailure)
            /\ WF_vars(Compare) /\ WF_vars(FollowChain) /\ WF_vars(PostCompare)
            /\ WF_vars(ResetFailure) /\ WF_vars(Increment)

Termination == <>(pc = "outer" /\ loopCounter >= (2 * inputLength))

====