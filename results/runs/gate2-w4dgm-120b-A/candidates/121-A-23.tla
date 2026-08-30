---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Replaces the natural-number type Nat everywhere in the module so that the
\* model is finite (and therefore checkable) while keeping the arithmetic.
\* The override is done in the .cfg by mapping CharacterSet to Nat.
\* EXTENDS Naturals is retained because Sequences and FiniteSets rely on it.
Nat == CharacterSet

Variable inputString, stringLength, failureFn, patIdx, loopIdx, bestOffset, pc

vars == <<inputString, stringLength, failureFn, patIdx, loopIdx, bestOffset, pc>>

Sentinel == 99
MaxLoop == 3
MaxLen == 3

TypeInvariant ==
  /\ inputString \in [1..MaxLen -> CharacterSet]
  /\ stringLength \in 0..MaxLen
  /\ failureFn \in [0..(2 * MaxLen) -> (0..(2 * MaxLen)) \cup {Sentinel}]
  /\ patIdx \in (0..(2 * MaxLen)) \cup {Sentinel}
  /\ loopIdx \in 0..(2 * MaxLen)
  /\ bestOffset \in 0..(MaxLen - 1)
  /\ pc \in {"outerLoop", "postTerminated"}

Init ==
  /\ inputString \in [1..MaxLen -> CharacterSet]
  /\ stringLength = Len(inputString)
  /\ failureFn = [k \in 0..(2 * MaxLen) |-> Sentinel]
  /\ patIdx = Sentinel
  /\ loopIdx = 1
  /\ bestOffset = 0
  /\ pc = "outerLoop"

InitFailureLookup ==
  /\ failureFn' = [failureFn EXCEPT ![loopIdx - 1] = Sentinel]
  /\ pc' = "postTerminated"
  /\ UNCHANGED <<inputString, stringLength, patIdx, loopIdx, bestOffset>>

\* Step (2): read the failure function for the current position, which is the
\* index into the doubled string (modulo the original length, handled when
\* accessing the sequence). This is always available, so it never blocks.
OuterLoop ==
  /\ pc = "outerLoop"
  /\ loopIdx < 2 * MaxLen
  /\ failureFn' = [failureFn EXCEPT ![loopIdx - 1] = Sentinel]
  /\ pc' = "postTerminated"
  /\ UNCHANGED <<inputString, stringLength, patIdx, loopIdx, bestOffset>>

\* Step (3): the inner while loop that walks backwards through the failure
\* chain as long as characters keep matching and the chain has not been
\* exhausted. A character mismatch aborts the loop early.
InnerComparison ==
  /\ pc = "postTerminated"
  /\ loopIdx < 2 * MaxLen
  /\ loopIdx < stringLength
  /\ inputString[loopIdx + 1] = inputString[(bestOffset + loopIdx) % stringLength + 1]
  /\ failureFn[loopIdx] # Sentinel
  /\ pc' = "postTerminated"
  /\ UNCHANGED <<inputString, stringLength, failureFn, patIdx, loopIdx, bestOffset>>

\* Step (4): the update triggered by a strictly smaller character in the same
\* position against the current best rotation.
UpdateOffsetOnStrictlySmaller ==
  /\ pc = "postTerminated"
  /\ loopIdx < stringLength
  /\ inputString[loopIdx + 1] < inputString[(bestOffset + loopIdx) % stringLength + 1]
  /\ bestOffset' = loopIdx
  /\ UNCHANGED <<inputString, stringLength, failureFn, patIdx, loopIdx, pc>>

\* Step (5): follow the failure function chain to the next candidate position.
FollowFailureChain ==
  /\ pc = "postTerminated"
  /\ failureFn[loopIdx] # Sentinel
  /\ patIdx' = failureFn[loopIdx]
  /\ pc' = "postTerminated"
  /\ UNCHANGED <<inputString, stringLength, failureFn, loopIdx, bestOffset>>

\* Step (6): the final compare once the failure chain is exhausted, plus
\* resetting or extending the failure entry.
CompareAndExtend ==
  /\ pc = "postTerminated"
  /\ failureFn[loopIdx] = Sentinel
  /\ loopIdx < stringLength
  /\ IF inputString[(bestOffset + loopIdx) % stringLength + 1] # inputString[loopIdx + 1]
       THEN IF inputString[loopIdx + 1] < inputString[(bestOffset + loopIdx) % stringLength + 1]
              THEN bestOffset' = loopIdx
              ELSE bestOffset' = bestOffset
       ELSE bestOffset' = bestOffset
  /\ failureFn' = [failureFn EXCEPT ![loopIdx] = IF failureFn[loopIdx] = Sentinel
                                            THEN Sentinel ELSE failureFn[loopIdx] + 1]
  /\ pc' = "postTerminated"
  /\ UNCHANGED <<inputString, stringLength, patIdx, loopIdx>>

\* Step (7): return to the outer loop check with the loop counter advanced.
IncrementLoop ==
  /\ pc = "postTerminated"
  /\ loopIdx' = loopIdx + 1
  /\ pc' = "outerLoop"
  /\ UNCHANGED <<inputString, stringLength, failureFn, patIdx, bestOffset>>

\* Step (8): the outer loop exhausted: the algorithm is done and stays put.
Terminate ==
  /\ pc = "outerLoop"
  /\ loopIdx >= 2 * MaxLen
  /\ pc' = "postTerminated"
  /\ UNCHANGED <<inputString, stringLength, failureFn, patIdx, loopIdx, bestOffset>>

\* Stuttering after termination: always available, so the model never gets
\* stuck forever in a live state.
Stutter ==
  /\ pc = "postTerminated"
  /\ loopIdx >= 2 * MaxLen
  /\ UNCHANGED vars

Next ==
  \/ InitFailureLookup
  \/ OuterLoop
  \/ InnerComparison
  \/ UpdateOffsetOnStrictlySmaller
  \/ FollowFailureChain
  \/ CompareAndExtend
  \/ IncrementLoop
  \/ Terminate
  \/ Stutter

Spec == Init /\ [][Next]_vars

\* The minimal rotation dominates every other rotation, and dominates strictly
\* unless the string is periodic with exactly that period.
Correctness ==
  /\ (stringLength = 0 \/ (bestOffset >= 0 /\ bestOffset < stringLength))
  /\ \A j \in 1..(stringLength - 1) :
       \A k \in 1..stringLength :
         inputString[(bestOffset + k) % stringLength + 1] <= inputString[(j + k) % stringLength + 1]
  /\ \A j \in 1..(stringLength - 1) :
       (\A k \in 1..stringLength :
          inputString[(bestOffset + k) % stringLength + 1] = inputString[(j + k) % stringLength + 1])
         => bestOffset <= j

Termination == []<>(pc = "postTerminated")

====