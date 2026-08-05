---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet

\* A character set that is a finite subset of the naturals; the config file
\* replaces Nat with this ZSequences-finite version so the model stays
\* bounded. EXTENDS Naturals is retained because the operators on the right
\* of the override (Nat) are defined in Naturals and we do not rename them.

ASSUME CharacterSet \subseteq Nat /\ CharacterSet # {}

VARIABLES inputString, stringLength, failureFunction, patternIndex,
          loopCounter, bestOffset, pc

vars == <<inputString, stringLength, failureFunction, patternIndex,
           loopCounter, bestOffset, pc>>

Sentinel == 999

\* All zero-indexed sequences over the character set up to the configured
\* maximum length are reachable from the start, so the algorithm is checked
\* against every input string of that size, not just a single fixed one.
StringCorpus == UNION { [1..n -> CharacterSet] : n \in 1..3 }

TypeOK ==
    /\ inputString \in StringCorpus
    /\ stringLength = Len(inputString)
    /\ failureFunction \in [0..2*stringLength -> Sentinel \cup (0..stringLength)]
    /\ patternIndex \in Sentinel \cup (0..stringLength)
    /\ loopCounter \in 1..(2*stringLength)
    /\ bestOffset \in 0..(stringLength - 1)
    /\ pc \in {"outerCheck", "lookup", "inner", "updateBest", "followFailure",
               "postCompare", "increment", "final"}

Init ==
    /\ inputString \in StringCorpus
    /\ stringLength = Len(inputString)
    /\ failureFunction = [i \in 0..(2*stringLength) |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

\* Outer loop over the doubled string (all rotations appear in its first
\* stringLength positions, the second half lets the failure chain unwind).
OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCounter < 2*stringLength
       THEN pc' = "lookup"
       ELSE pc' = "final"
    /\ UNCHANGED <<inputString, stringLength, failureFunction,
                   patternIndex, loopCounter, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ patternIndex' = failureFunction[loopCounter - bestOffset]
    /\ pc' = "inner"
    /\ UNCHANGED <<inputString, stringLength, failureFunction,
                   loopCounter, bestOffset>>

\* Compare the character at the current loop position against the one at
\* the candidate position (bestOffset), wrapping around with Modulo.
InnerLoop ==
    /\ pc = "inner"
    /\ IF inputString[(loopCounter % stringLength) + 1]
          # inputString[((loopCounter - patternIndex) % stringLength) + 1]
         /\ patternIndex # Sentinel
       THEN pc' = "inner"
       ELSE pc' = "postCompare"
    /\ UNCHANGED <<inputString, stringLength, failureFunction,
                   patternIndex, loopCounter, bestOffset>>

UpdateBestWhenLess ==
    /\ pc = "postCompare"
    /\ inputString[(loopCounter % stringLength) + 1]
          # inputString[((loopCounter - patternIndex) % stringLength) + 1]
    /\ patternIndex = Sentinel
    /\ inputString[(loopCounter % stringLength) + 1]
         < inputString[((loopCounter - patternIndex) % stringLength) + 1]
    /\ bestOffset < loopCounter
    /\ bestOffset' = loopCounter
    /\ UNCHANGED <<inputString, stringLength, failureFunction,
                   patternIndex, loopCounter, pc>>

FollowFailure ==
    /\ pc = "postCompare"
    /\ patternIndex # Sentinel
    /\ patternIndex' = failureFunction[patternIndex]
    /\ pc' = "postCompare"
    /\ UNCHANGED <<inputString, stringLength, failureFunction,
                   loopCounter, bestOffset>>

ResetFailure ==
    /\ pc = "postCompare"
    /\ patternIndex = Sentinel
    /\ failureFunction' = [failureFunction EXCEPT ![loopCounter - bestOffset] = Sentinel]
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, stringLength, patternIndex,
                   loopCounter, bestOffset>>

ExtendFailure ==
    /\ pc = "postCompare"
    /\ patternIndex # Sentinel
    /\ patternIndex < stringLength
    /\ failureFunction' = [failureFunction EXCEPT ![loopCounter - bestOffset] = patternIndex + 1]
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, stringLength, patternIndex,
                   loopCounter, bestOffset>>

IncrementCounter ==
    /\ pc = "increment"
    /\ loopCounter < 2*stringLength
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, stringLength, failureFunction,
                   patternIndex, bestOffset>>

Stall ==
    /\ pc = "final"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ Lookup \/ InnerLoop \/ UpdateBestWhenLess \/ FollowFailure
    \/ ResetFailure \/ ExtendFailure \/ IncrementCounter \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup)
                 /\ WF_vars(InnerLoop) /\ WF_vars(PostCompare)
                 /\ WF_vars(IncrementCounter)

\* Upon termination the best rotation offset is the lexicographically
\* minimal rotation, and among equal rotations it is the smallest shift.
Correctness ==
    (pc = "final") =>
      /\ \A i \in 0..(stringLength - 1)
            : inputString[(i % stringLength) + 1]
                >= inputString[(bestOffset % stringLength) + 1]
      /\ \A i \in 0..(stringLength - 1)
            : (inputString[(i % stringLength) + 1]
                  = inputString[(bestOffset % stringLength) + 1])
                => (bestOffset <= i)

Termination == <>(pc = "final")

====