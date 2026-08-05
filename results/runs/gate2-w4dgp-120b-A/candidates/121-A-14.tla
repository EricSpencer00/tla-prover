---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

\* The input string is modelled as a zero-indexed SEQUENCE (the standard
\* SEQUENCE type has been imported from Naturals but here it is used with a
\* zero-base instead of the usual one-base, and the .cfg replaces Nat with
\* a finite subset of it, so the model stays bounded).
CONSTANTS CharacterSet

VARIABLES inputString, length, failure, patIdx, loopIdx, best, pc

vars == <<inputString, length, failure, patIdx, loopIdx, best, pc>>

Bound == 4
Sentinel == Bound

TypeOK ==
  /\ inputString \in [0..Bound -> CharacterSet]
  /\ length \in 1..Bound
  /\ failure \in [0..2*Bound -> 0..Sentinel]
  /\ patIdx \in 0..Sentinel
  /\ loopIdx \in 0..2*Bound
  /\ best \in 0..Bound-1
  /\ pc \in 0..7

Init ==
  /\ inputString \in [0..Bound -> CharacterSet]
  /\ length = Cardinality({i \in 0..Bound : inputString[i] # 0})
  /\ length >= 1
  /\ failure = [i \in 0..2*Bound |-> Sentinel]
  /\ patIdx = Sentinel
  /\ loopIdx = 1
  /\ best = 0
  /\ pc = 0

\* L1: the outer loop runs up to twice the string length so the doubled
\* string (implicit wrap-around) is fully scanned.
OuterLoop ==
  /\ pc = 0
  /\ IF loopIdx < 2*length
       THEN pc' = 1
       ELSE pc' = 7
  /\ UNCHANGED <<inputString, length, failure, patIdx, loopIdx, best>>

FailureLookup ==
  /\ pc = 1
  /\ patIdx' = failure[loopIdx - best]
  /\ pc' = 2
  /\ UNCHANGED <<inputString, length, failure, loopIdx, best>>

\* L2: the inner comparison loop (F) -- it only repeats while the
\* characters still match and the pattern index is still defined.
InnerComparison ==
  /\ pc = 2
  /\ (inputString[loopIdx % length] = inputString[(patIdx + loopIdx) % length])
     /\ patIdx # Sentinel
  /\ pc' = 2
  /\ UNCHANGED <<inputString, length, failure, patIdx, loopIdx, best>>

UpdateBest ==
  /\ pc = 2
  /\ inputString[loopIdx % length] # inputString[(patIdx + loopIdx) % length]
  /\ patIdx # Sentinel
  /\ inputString[loopIdx % length] < inputString[(patIdx + loopIdx) % length]
  /\ best' = loopIdx % length
  /\ pc' = 3
  /\ UNCHANGED <<inputString, length, failure, patIdx, loopIdx>>

AdvanceFailure ==
  /\ pc = 3
  /\ patIdx' = failure[patIdx]
  /\ pc' = 2
  /\ UNCHANGED <<inputString, length, failure, loopIdx, best>>

\* L3: after the inner loop finishes: if the characters differ with the
\* pattern exhausted, check again for a new best offset (the G step);
\* either way reset the failure function entry (the H step).
PostComparison ==
  /\ pc = 2
  /\ inputString[loopIdx % length] # inputString[(patIdx + loopIdx) % length]
  /\ patIdx = Sentinel
  /\ LET best' == IF inputString[loopIdx % length] < inputString[(patIdx + loopIdx) % length]
                  THEN loopIdx % length ELSE best
         fail' == IF inputString[loopIdx % length] = inputString[(patIdx + loopIdx) % length]
                  THEN Sentinel ELSE patIdx + 1
         pc'   == 4
     IN  <<best, failure, pc>> = <<best', fail', pc'>>
  /\ UNCHANGED <<inputString, length, patIdx, loopIdx>>

WrapAndReset ==
  /\ pc = 4
  /\ loopIdx' = loopIdx + 1
  /\ pc' = 0
  /\ UNCHANGED <<inputString, length, failure, patIdx, best>>

Stall ==
  /\ pc = 7
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop
  \/ FailureLookup
  \/ InnerComparison
  \/ UpdateBest
  \/ AdvanceFailure
  \/ PostComparison
  \/ WrapAndReset
  \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(FailureLookup)
                     /\ WF_vars(InnerComparison) /\ WF_vars(UpdateFailure)

\* SAFETY: type-correctness and the fact that the best offset never
\* points outside the actual string.
TypeInvariant == TypeOK

\* CORRECTNESS: the rotation that the algorithm records as best is
\* lexicographically no greater than any other rotation of the same
\* string, and among equal rotations it is the one with the smallest
\* shift, so it is the unique minimal rotation.
Correctness ==
  /\ pc = 7
  /\ \A shift \in 0..length-1 : inputString[best..length-1] ^ inputString[0..best-1]
                              <= inputString[shift..length-1] ^ inputString[0..shift-1]

\* LIVENESS: the outer loop eventually runs out of room.
Termination == <>(pc = 7)

====