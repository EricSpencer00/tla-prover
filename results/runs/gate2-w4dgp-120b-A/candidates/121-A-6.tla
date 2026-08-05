---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  CharacterSet

\* A ZSequences character set is the natural-number alphabet 'Nat' redefined
\* as a finite set for model checking; this replaces the Nat imported from
\* Naturals with a bounded version without breaking any other imports.
ZSequences == CharacterSet

MaxLength == 2
Undefined == 255

VARIABLES
  inputString
  stringLength
  failureFunction
  patternIndex
  loopCounter
  bestOffset
  pc

vars == <<inputString, stringLength, failureFunction, patternIndex,
          loopCounter, bestOffset, pc>>

TypeInvariant ==
  /\ inputString \in [0..MaxLength -> ZSequences]
  /\ stringLength = Len(inputString)
  /\ failureFunction \in [0..2*MaxLength -> 0..Undefined]
  /\ patternIndex \in 0..Undefined
  /\ loopCounter \in 0..2*MaxLength
  /\ bestOffset \in 0..MaxLength
  /\ pc \in {"outerLoop", "failureLookup", "innerLoop", "failureChain",
             "postComparison", "incrementCounter"}

Init ==
  /\ inputString \in [0..MaxLength -> ZSequences]
  /\ stringLength = Len(inputString)
  /\ failureFunction = [i \in 0..2*MaxLength |-> Undefined]
  /\ patternIndex = Undefined
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerLoop"

OuterLoop ==
  /\ pc = "outerLoop"
  /\ IF loopCounter < 2*stringLength
       THEN /\ pc' = "failureLookup"
            /\ UNCHANGED <<inputString, stringLength, failureFunction,
                          patternIndex, loopCounter, bestOffset>>
       ELSE /\ pc' = "incrementCounter"
            /\ UNCHANGED <<inputString, stringLength, failureFunction,
                          patternIndex, loopCounter, bestOffset>>
  /\ UNCHANGED pc

FailureLookup ==
  /\ pc = "failureLookup"
  /\ failureFunction' = [failureFunction EXCEPT
                         ![loopCounter MOD stringLength] =
                           failureFunction[(loopCounter + bestOffset) MOD stringLength]]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, stringLength, patternIndex, loopCounter,
                bestOffset>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ (inputString[loopCounter MOD stringLength] # inputString[(loopCounter + bestOffset) MOD stringLength])
  /\ patternIndex # Undefined
  /\ pc' = "failureChain"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex,
                loopCounter, bestOffset>>

UpdateBestLess ==
  /\ inputString[loopCounter MOD stringLength] < inputString[(loopCounter + bestOffset) MOD stringLength]
  /\ bestOffset' = (bestOffset + loopCounter) MOD stringLength
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex,
                loopCounter, pc>>

FailureChain ==
  /\ pc = "failureChain"
  /\ patternIndex' = failureFunction[patternIndex]
  /\ bestOffset' = IF inputString[loopCounter MOD stringLength] <
                        inputString[(loopCounter + bestOffset) MOD stringLength]
                    THEN (bestOffset + loopCounter) MOD stringLength
                    ELSE bestOffset
  /\ pc' = "postComparison"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, loopCounter>>

PostComparison ==
  /\ pc = "postComparison"
  /\ (inputString[loopCounter MOD stringLength] # inputString[(loopCounter + bestOffset) MOD stringLength])
  /\ patternIndex = Undefined
  /\ IF inputString[loopCounter MOD stringLength] <
        inputString[(loopCounter + bestOffset) MOD stringLength]
     THEN bestOffset' = (bestOffset + loopCounter) MOD stringLength
     ELSE bestOffset' = bestOffset
  /\ failureFunction' = [failureFunction EXCEPT
                         ![(loopCounter + bestOffset) MOD stringLength] =
                           IF patternIndex = Undefined THEN Undefined
                           ELSE patternIndex + 1]
  /\ pc' = "incrementCounter"
  /\ UNCHANGED <<inputString, stringLength, patternIndex, loopCounter>>

IncrementCounter ==
  /\ pc = "incrementCounter"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerLoop"
  /\ UNCHANGED <<inputString, stringLength, failureFunction, patternIndex,
                bestOffset>>

Stall ==
  /\ pc = "incrementCounter"
  /\ loopCounter >= 2*stringLength
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ FailureLookup \/ InnerLoop \/ FailureChain
  \/ PostComparison \/ IncrementCounter \/ Stall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(OuterLoop)
  /\ WF_vars(FailureLookup)
  /\ WF_vars(InnerLoop)
  /\ WF_vars(FailureChain)
  /\ WF_vars(PostComparison)
  /\ WF_vars(IncrementCounter)

\* Termination: the algorithm eventually reaches its final, stalled state.
Termination == <>(pc = "incrementCounter" /\ loopCounter >= 2*stringLength)

\* Correctness: the best offset identifies the lexicographically-minimal
\* rotation, breaking ties in favor of the smallest offset.
Correctness ==
  \A i \in 0..stringLength-1 :
    ((\A j \in 0..stringLength-1 :
        inputString[(i + j) MOD stringLength] <= inputString[(bestOffset + j) MOD stringLength])
      => (i >= bestOffset))

====