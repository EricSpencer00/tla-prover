---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet

\* Sequences over a finite character set. The model's alphabet size is bounded by the
\* CharacterSet constant, which is redefined by the .cfg to be a FINITE version of Nat.
ZSequences == UNION { [1..n -> CharacterSet] : n \in Nat }

VARIABLES string, length, failure, patIdx, loopCounter, bestOffset, pc

vars == <<string, length, failure, patIdx, loopCounter, bestOffset, pc>>

Sentinel == 0xFFFFFFFF

TypeOK ==
  /\ string \in ZSequences /\ length = Len(string)
  /\ failure \in [0..(2*length) -> Nat \cup {Sentinel}]
  /\ patIdx \in Nat \cup {Sentinel}
  /\ loopCounter \in Nat
  /\ bestOffset \in Nat
  /\ pc \in {1, 2, 3, 4, 5, 6, 7}

Init ==
  /\ string \in ZSequences /\ length = Len(string)
  /\ failure = [i \in 0..(2*length) |-> Sentinel]
  /\ patIdx = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = 1

\* Outer loop; terminates once the counter reaches the end of the doubled string.
OuterCheck ==
  /\ pc = 1
  /\ IF loopCounter < 2 * length
       THEN pc' = 2
       ELSE pc' = 7
  /\ UNCHANGED <<string, length, failure, patIdx, loopCounter, bestOffset>>

\* Failure function lookup for the current position relative to the best offset.
FailureLookup ==
  /\ pc = 2
  /\ patIdx' = failure[(loopCounter + bestOffset) % length]
  /\ pc' = 3
  /\ UNCHANGED <<string, length, failure, loopCounter, bestOffset>>

\* Inner comparison loop: compare the candidate character to the best-offset character.
InnerCompare ==
  /\ pc = 3
  /\ IF string[(loopCounter + bestOffset) % length] = string[(loopCounter + patIdx) % length]
       THEN pc' = 5
       ELSE IF patIdx # Sentinel
              THEN pc' = 3
              ELSE pc' = 4
  /\ UNCHANGED <<string, length, failure, patIdx, loopCounter, bestOffset>>

\* If the current character is strictly less, the candidate becomes best.
UpdateBestLT ==
  /\ pc = 4
  /\ bestOffset' = IF string[(loopCounter + bestOffset) % length] < string[(loopCounter + patIdx) % length]
                     THEN bestOffset + loopCounter
                     ELSE bestOffset
  /\ pc' = 5
  /\ UNCHANGED <<string, length, failure, patIdx, loopCounter>>

FollowFailure ==
  /\ pc = 5
  /\ patIdx' = failure[patIdx]
  /\ pc' = 6
  /\ UNCHANGED <<string, length, failure, loopCounter, bestOffset>>

\* Post-compare: on a final mismatch, update best if needed and reset/extend failure.
PostCompare ==
  /\ pc = 6
  /\ IF string[(loopCounter + bestOffset) % length] # string[(loopCounter + patIdx) % length]
       THEN bestOffset' = IF string[(loopCounter + bestOffset) % length] < string[(loopCounter + patIdx) % length]
                            THEN bestOffset + loopCounter
                            ELSE bestOffset
            ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![(loopCounter + bestOffset) % length] =
                  IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
  /\ pc' = 7
  /\ UNCHANGED <<string, length, patIdx, loopCounter>>

\* Increment the loop counter and return to the outer check.
NextIteration ==
  /\ pc = 7
  /\ loopCounter' = loopCounter + 1
  /\ pc' = 1
  /\ UNCHANGED <<string, length, failure, patIdx, bestOffset>>

\* The algorithm has terminated; it simply waits here.
Stall ==
  /\ pc = 7 /\ loopCounter >= 2 * length
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ FailureLookup \/ InnerCompare \/ UpdateBestLT
  \/ FollowFailure \/ PostCompare \/ NextIteration \/ Stall

Spec == INIT /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup)
        /\ WF_vars(InnerCompare) /\ WF_vars(UpdateBestLT) /\ WF_vars(FollowFailure)
        /\ WF_vars(PostCompare) /\ WF_vars(NextIteration)

\* Upon termination, the best offset yields the lexicographically-minimal rotation,
\* and among equal rotations it is the smallest shift value.
Correctness ==
  /\ pc = 7 /\ loopCounter >= 2 * length
  /\ \A i \in Nat :
       i < length => string[(bestOffset + i) % length] <= string[(i) % length]
  /\ (\A j \in Nat :
        j < length =>
          (string[(bestOffset + j) % length] = string[(j) % length]) => bestOffset <= j)

Termination == <>(pc = 7 /\ loopCounter >= 2 * length)

====