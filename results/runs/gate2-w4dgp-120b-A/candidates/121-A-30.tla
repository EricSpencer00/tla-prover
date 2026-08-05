---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

ASSUME /\ CharacterSet # {}
       /\ CharacterSet \subseteq Nat

VARIABLES inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset, pc
vars == <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset, pc>>

MaxChars == 3
MaxLen == 3
Undefined == 99

SeqDomain(S) == {s \in Seq(CharacterSet) : Len(s) <= MaxLen}

Init ==
  /\ inputString \in SeqDomain(CharacterSet)
  /\ inputString # {}
  /\ stringLength = Len(inputString)
  /\ failureFunction \in [0..(2 * MaxLen) -> 0..(MaxLen + 1)]
  /\ \A i \in 0..(2 * MaxLen) : failureFunction[i] = Undefined
  /\ patternIndex = Undefined
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

OuterLoopCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCounter < (2 * stringLength)
     THEN pc' = "failureLookup"
     ELSE pc' = "finished"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset>>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ patternIndex' = failureFunction[loopCounter - bestOffset]
  /\ pc' = "innerCompare"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, loopCounter, bestOffset>>

InnerLoopCompare ==
  /\ pc = "innerCompare"
  /\ inputString[(loopCounter % stringLength) + 1] # inputString[((bestOffset + patternIndex) % stringLength) + 1]
  /\ patternIndex # Undefined
  /\ pc' = "followFailure"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset>>

UpdateBestOnLess ==
  /\ pc = "innerCompare"
  /\ inputString[(loopCounter % stringLength) + 1] < inputString[((bestOffset + patternIndex) % stringLength) + 1]
  /\ bestOffset' = loopCounter % stringLength
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter, pc>>

FollowFailure ==
  /\ pc = "followFailure"
  /\ patternIndex' = failureFunction[patternIndex - bestOffset]
  /\ pc' = "postCompare"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, loopCounter, bestOffset>>

PostComparison ==
  /\ pc = "postComparison"
  /\ LET
       updateEntry == IF patternIndex = Undefined
                       THEN failureFunction[loopCounter - bestOffset] = Undefined
                       ELSE failureFunction[loopCounter - bestOffset] = patternIndex + 1
       updateBest == IF inputString[(loopCounter % stringLength) + 1] < inputString[((bestOffset + patternIndex) % stringLength) + 1]
                       THEN loopCounter % stringLength
                       ELSE bestOffset
     IN /\ updateEntry
        /\ bestOffset' = updateBest
        /\ pc' = "incrementLoop"
        /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter>>

IncrementLoop ==
  /\ pc = "incrementLoop"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, bestOffset>>

Stutter ==
  /\ pc = "finished"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoopCheck
  \/ FailureLookup
  \/ InnerLoopCompare
  \/ UpdateBestOnLess
  \/ FollowFailure
  \/ PostComparison
  \/ IncrementLoop
  \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(FailureLookup) /\ WF_vars(InnerLoopCompare) /\ WF_vars(FollowFailure) /\ WF_vars(PostComparison) /\ WF_vars(IncrementLoop)

TypeInvariant ==
  /\ inputString \in SeqDomain(CharacterSet)
  /\ stringLength = Len(inputString)
  /\ \A i \in 0..(2 * MaxLen) : failureFunction[i] \in 0..(MaxLen + 1)
  /\ patternIndex \in 0..(MaxLen + 1)
  /\ loopCounter \in 0..(2 * MaxLen)
  /\ bestOffset \in 0..(MaxLen - 1)

Correctness ==
  /\ pc = "finished"
  /\ \A offset \in 0..(stringLength - 1) :
       \/ (inputString[(bestOffset % stringLength) + 1] < inputString[((offset + bestOffset - bestOffset) % stringLength) + 1])
       \/ (inputString[(bestOffset % stringLength) + 1] = inputString[((offset + bestOffset - bestOffset) % stringLength) + 1] /\ bestOffset <= offset)

Termination == <>(pc = "finished")
====