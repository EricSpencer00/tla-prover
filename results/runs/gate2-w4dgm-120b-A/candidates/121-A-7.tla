---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, ZSequences

\* The lexicographically-least circular substring algorithm from Booth (1980)
\* builds a KMP-style failure function while scanning a doubled string, then
\* uses the function to skip forward over equal-character runs.  The state
\* variables are the input string, its length, the failure array, the current
\* pattern-match index, the outer-loop counter, the best rotation offset, and
\* the program counter over the algorithm's labeled steps.
\*
\* Correctness means that the rotation at the best offset is not greater than
\* any other rotation of the same string, and that ties are broken by the
\* smallest shift value.

CONSTANT CharacterSet

MaxLen == 2
MaxPos == 2 * MaxLen - 1
MaxChar == 1
Sentinel == MaxPos + 1
Indices == 0 .. MaxPos

VARIABLES source, length, failure, matchIndex, loopPos, bestOffset, pc

vars == <<source, length, failure, matchIndex, loopPos, bestOffset, pc>>

Rotations(s) == { s[(i + offset) % Len(s)] : offset \in 0 .. (Len(s) - 1) }

TypeInvariant ==
  /\ source \in [Indices -> {0, 1}]
  /\ length \in 0 .. MaxLen
  /\ failure \in [Indices -> 0 .. (MaxPos + 1)]
  /\ matchIndex \in 0 .. (MaxPos + 1)
  /\ loopPos \in 0 .. MaxPos
  /\ bestOffset \in 0 .. MaxLen
  /\ pc \in 0 .. 7

Init ==
  /\ source = [i \in Indices |-> IF i > MaxChar THEN 0 ELSE i]
  /\ length = MaxLen
  /\ failure = [i \in Indices |-> Sentinel]
  /\ matchIndex = Sentinel
  /\ loopPos = 1
  /\ bestOffset = 0
  /\ pc = 0

\* Outer loop: compare positions up to just below twice the length of the
\* string (the algorithm works over a doubled string).
OuterLoop ==
  /\ loopPos < MaxPos
  /\ pc' = 1
  /\ UNCHANGED <<source, length, failure, matchIndex, loopPos, bestOffset>>

\* Retrieve the failure function entry for the current offset candidate.
LookupFailure ==
  /\ pc = 1
  /\ matchIndex' = failure[bestOffset]
  /\ pc' = 2
  /\ UNCHANGED <<source, length, failure, loopPos, bestOffset>>

\* The inner loop follows the KMP failure chain while characters differ.
InnerLoop ==
  /\ pc = 2
  /\ source[loopPos % length] # source[(loopPos + matchIndex) % length]
  /\ \/ matchIndex # Sentinel
     \/ pc' = 3
  /\ UNCHANGED <<source, length, failure, loopPos, bestOffset>>

\* The character at the current rotation is less: record this shift as the
\* best offset so far.
UpdateBest ==
  /\ pc = 2
  /\ source[loopPos % length] < source[(loopPos + matchIndex) % length]
  /\ bestOffset' = loopPos
  /\ pc' = 3
  /\ UNCHANGED <<source, length, failure, matchIndex, loopPos>>

\* Follow the failure chain (one step forward along the KMP path).
FollowChain ==
  /\ pc = 3
  /\ matchIndex' = failure[matchIndex]
  /\ pc' = 4
  /\ UNCHANGED <<source, length, failure, loopPos, bestOffset>>

\* If the characters still differ and the failure chain is exhausted, the
\* current position is a new candidate; otherwise the failure entry is
\* extended by one on the basis of the current pattern match length.
PostCompare ==
  /\ pc = 4
  /\ LET newFail == IF source[loopPos % length] < source[(loopPos + matchIndex) % length]
                     THEN Sentinel
                     ELSE IF matchIndex = Sentinel THEN 0 ELSE matchIndex + 1
       newBest == IF /\ source[loopPos % length] < source[(loopPos + matchIndex) % length]
                      /\ matchIndex = Sentinel
                    THEN loopPos ELSE bestOffset
   IN /\ failure' = [failure EXCEPT ![bestOffset] = newFail]
      /\ bestOffset' = newBest
  /\ pc' = 5
  /\ UNCHANGED <<source, length, matchIndex, loopPos>>

CheckEnd ==
  /\ pc = 5
  /\ loopPos' = loopPos + 1
  /\ pc' = 0
  /\ UNCHANGED <<source, length, failure, matchIndex, bestOffset>>

Stutter ==
  /\ pc = 5
  /\ loopPos = MaxPos
  /\ UNCHANGED vars

Next == OuterLoop \/ LookupFailure \/ InnerLoop \/ UpdateBest \/ FollowChain \/ PostCompare \/ CheckEnd \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(LookupFailure) /\ WF_vars(InnerLoop) /\ WF_vars(UpdateBest) /\ WF_vars(FollowChain) /\ WF_vars(PostCompare) /\ WF_vars(CheckEnd)

\* Under termination the best rotation is not greater than any other, and
\* ties are broken by the smallest shift value.
Correctness ==
  /\ loopPos = MaxPos
  /\ loopPos' = loopPos
  /\ \A x \in Rotations(source) : source[bestOffset] <= x
  /\ \A offset \in 0 .. (Len(source) - 1) :
       (source[bestOffset] = source[offset] => bestOffset <= offset)

Termination == WF_vars(OuterLoop) /\ WF_vars(CheckEnd)

====