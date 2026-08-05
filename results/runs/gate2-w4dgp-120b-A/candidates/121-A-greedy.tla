---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CharacterSet

VARIABLES inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset, pc

vars == <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset, pc>>

Sentinel == -1

TypeInvariant ==
  /\ inputString \in [1..stringLength -> CharacterSet]
  /\ stringLength \in Nat
  /\ failureFunction \in [0..(2 * stringLength) -> (0..(2 * stringLength)) \cup {Sentinel}]
  /\ patternIndex \in (0..(2 * stringLength)) \cup {Sentinel}
  /\ loopCounter \in 0..(2 * stringLength)
  /\ bestOffset \in 0..(stringLength - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateBest", "followFailure", "postCompare", "increment", "done"}

Init ==
  /\ \E s \in [1..stringLength -> CharacterSet] : inputString = s
  /\ stringLength = Len(inputString)
  /\ failureFunction = [i \in 0..(2 * stringLength) |-> Sentinel]
  /\ patternIndex = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCounter < (2 * stringLength)
       THEN /\ pc' = "lookup"
            /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset>>
       ELSE /\ pc' = "done"
            /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ patternIndex' = failureFunction[(loopCounter - bestOffset) % stringLength]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, loopCounter, bestOffset>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ IF inputString[(loopCounter % stringLength) + 1] # inputString[((loopCounter - patternIndex) % stringLength) + 1]
       THEN IF patternIndex # Sentinel
              THEN /\ pc' = "followFailure"
                   /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset>>
              ELSE /\ pc' = "postCompare"
                   /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset>>
       ELSE /\ pc' = "increment"
            /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter, bestOffset>>

UpdateBest ==
  /\ pc = "updateBest"
  /\ inputString[(loopCounter % stringLength) + 1] < inputString[((loopCounter - patternIndex) % stringLength) + 1]
  /\ bestOffset' = loopCounter % stringLength
  /\ pc' = "followFailure"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, loopCounter>>

FollowFailure ==
  /\ pc = "followFailure"
  /\ patternIndex' = failureFunction[patternIndex]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, loopCounter, bestOffset>>

PostCompare ==
  /\ pc = "postCompare"
  /\ inputString[(loopCounter % stringLength) + 1] # inputString[((loopCounter - patternIndex) % stringLength) + 1]
  /\ patternIndex = Sentinel
  /\ bestOffset' = IF inputString[(loopCounter % stringLength) + 1] < inputString[((loopCounter - patternIndex) % stringLength) + 1]
                    THEN loopCounter % stringLength
                    ELSE bestOffset
  /\ failureFunction' = [failureFunction EXCEPT ![(loopCounter - bestOffset) % stringLength] = IF patternIndex = Sentinel THEN Sentinel ELSE patternIndex + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, stringLength, patternIndex, loopCounter>>

Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ UpdateBest
  \/ FollowFailure
  \/ PostCompare
  \/ Increment
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup) /\ WF_vars(InnerLoop) /\ WF_vars(UpdateBest) /\ WF_vars(FollowFailure) /\ WF_vars(PostCompare) /\ WF_vars(Increment)

Correctness ==
  /\ \A i \in 0..(stringLength - 1) :
       LET rotationAt(k) == [j \in 1..stringLength |-> inputString[((k + j - 1) % stringLength) + 1]]
       IN rotationAt(bestOffset) <= rotationAt(i)
  /\ \A i \in 0..(stringLength - 1) :
       (rotationAt(bestOffset) = rotationAt(i)) => (bestOffset <= i)

Termination == <>(pc = "done")

====