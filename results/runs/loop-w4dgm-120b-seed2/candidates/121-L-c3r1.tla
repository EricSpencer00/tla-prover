---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Zero-indexed sequences over the character set (a subset of Nat); the
\* alphabet is finite, so the model stays within bounded state space.
Corpus == [1..n \in Nat |-> IF n = 0 THEN <<>> ELSE <<CHOOSE c \in CharacterSet : TRUE>> \o Corpus[n - 1]]

ASSERT Corpus \in FiniteSets

None == 0
MaxLen == 3

VARIABLES string, length, failure, patternIndex, loopCounter, bestOffset, pc

vars == <<string, length, failure, patternIndex, loopCounter, bestOffset, pc>>

TypeInvariant ==
  /\ string \in Corpus
  /\ length = Len(string)
  /\ failure \in [0..2 * MaxLen -> 0..MaxLen]
  /\ patternIndex \in 0..MaxLen
  /\ loopCounter \in 1..(2 * MaxLen + 1)
  /\ bestOffset \in 0..MaxLen
  /\ pc \in {"outerLoop", "failureLookup", "innerLoop", "postComparison", "done"}

\* The lexicographically smallest rotation is the one at bestOffset; it is
\* less than or equal to every other rotation, and any equal rotation is
\* displaced by a larger shift, so it is the minimal shift of the minimal string.
Correctness ==
  /\ pc = "done"
  /\ \A i \in 1..length : string[(bestOffset + i) % length] <= string[(i - 1) % length]
  /\ \A i \in 1..length :
        (string[(bestOffset + i) % length] = string[(i - 1) % length]) => (bestOffset <= i - 1)

Init ==
  /\ \E s \in Corpus : string = s
  /\ length = Len(string)
  /\ failure = [i \in 0..(2 * MaxLen) |-> None]
  /\ patternIndex = None
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerLoop"

OuterLoop ==
  /\ pc = "outerLoop"
  /\ IF loopCounter <= 2 * length THEN pc' = "failureLookup" ELSE pc' = "done"
  /\ UNCHANGED <<string, length, failure, patternIndex, loopCounter, bestOffset>>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ patternIndex' = failure[loopCounter - 1]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<string, length, failure, loopCounter, bestOffset>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET curChar == string[(loopCounter - 1) % length]
         candChar == string[(bestOffset + patternIndex) % length]
         advance == IF curChar < candChar THEN bestOffset' = loopCounter - 1 ELSE bestOffset'
     IN
       /\ IF curChar # candChar /\ patternIndex # None
            THEN pc' = "innerLoop"
            ELSE pc' = "postComparison"
       /\ advance
  /\ UNCHANGED <<string, length, failure, patternIndex, loopCounter>>

PostComparison ==
  /\ pc = "postComparison"
  /\ LET curChar == string[(loopCounter - 1) % length]
         candChar == string[(bestOffset + patternIndex) % length]
         advance == IF (curChar # candChar /\ patternIndex = None /\ curChar < candChar)
                         THEN loopCounter + 1
                         ELSE loopCounter + 1
         newFailure == IF curChar # candChar /\ patternIndex = None
                         THEN failure
                         ELSE [failure EXCEPT ![loopCounter] =
                                IF curChar # candChar THEN patternIndex + 1 ELSE None]
         advanceOffset == IF (curChar # candChar /\ patternIndex = None /\ curChar < candChar)
                            THEN loopCounter - 1 ELSE bestOffset
     IN
       /\ loopCounter' = advance
       /\ failure' = newFailure
       /\ bestOffset' = advanceOffset
  /\ pc' = "outerLoop"
  /\ UNCHANGED <<string, length, patternIndex>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop
  \/ FailureLookup
  \/ InnerLoop
  \/ PostComparison
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(FailureLookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(PostComparison)

Termination == <>(pc = "done")

====