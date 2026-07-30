---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

(* The character set is a finite subset of Nat, so the model stays finite. *)
CONSTANTS CharacterSet

ModSuccessor(a, n) == (a + 1) % n

SequenceSpace(n) == [k \in 0 .. (n - 1) -> CharacterSet]

VARIABLES inputString, strLength, failure, patIdx, loopCnt, bestOffset, pc

vars == <<inputString, strLength, failure, patIdx, loopCnt, bestOffset, pc>>

TypeOK ==
  /\ inputString \in SequenceSpace(strLength)
  /\ strLength \in Nat
  /\ failure \in [0 .. (2 * strLength)] -> (0 .. (2 * strLength) \cup {99})
  /\ patIdx \in (0 .. (2 * strLength)) \cup {99}
  /\ loopCnt \in Nat
  /\ bestOffset \in Nat
  /\ pc \in {"outer", "failLookup", "compare", "updateOffset", "followFail",
             "postCompare", "increment", "done"}

Init ==
  /\ \E s \in SequenceSpace(1) : inputString = s
  /\ strLength = Len(inputString)
  /\ failure = [i \in 0 .. (2 * strLength) |-> 99]
  /\ patIdx = 99
  /\ loopCnt = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF loopCnt < (2 * strLength)
     THEN pc' = "failLookup"
     ELSE pc' = "done"
  /\ UNCHANGED <<inputString, strLength, failure, patIdx, loopCnt, bestOffset>>

FailLookup ==
  /\ pc = "failLookup"
  /\ patIdx' = failure[ModSuccessor(bestOffset, strLength)]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, strLength, failure, loopCnt, bestOffset>>

CompareStep ==
  /\ pc = "compare"
  /\ IF inputString[loopCnt % strLength] # inputString[patIdx % strLength]
       /\ patIdx # 99
     THEN pc' = "compare"
     ELSE pc' = "postCompare"
  /\ UNCHANGED <<inputString, strLength, failure, patIdx, loopCnt, bestOffset>>

UpdateOffset ==
  /\ pc = "updateOffset"
  /\ inputString[loopCnt % strLength] < inputString[patIdx % strLength]
  /\ bestOffset' = loopCnt % strLength
  /\ pc' = "followFail"
  /\ UNCHANGED <<inputString, strLength, failure, patIdx, loopCnt>>

FollowFail ==
  /\ pc = "followFail"
  /\ patIdx' = failure[patIdx]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, strLength, failure, loopCnt, bestOffset>>

PostCompareStep ==
  /\ pc = "postCompare"
  /\ IF inputString[loopCnt % strLength] # inputString[patIdx % strLength]
        /\ patIdx = 99
        /\ inputString[loopCnt % strLength] < inputString[patIdx % strLength]
     THEN bestOffset' = loopCnt % strLength
     ELSE bestOffset' = bestOffset
  /\ failure' = IF patIdx = 99
                 THEN [failure EXCEPT ![ModSuccessor(bestOffset, strLength)] = 99]
                 ELSE [failure EXCEPT ![ModSuccessor(bestOffset, strLength)] = patIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLength, patIdx, loopCnt>>

Increment ==
  /\ pc = "increment"
  /\ loopCnt' = loopCnt + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, strLength, failure, patIdx, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop
  \/ FailLookup
  \/ CompareStep
  \/ UpdateOffset
  \/ FollowFail
  \/ PostCompareStep
  \/ Increment
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(FailLookup)
        /\ WF_vars(CompareStep) /\ WF_vars(UpdateOffset) /\ WF_vars(FollowFail)
        /\ WF_vars(PostCompareStep) /\ WF_vars(Increment)

TypeInvariant == TypeOK

Correctness ==
  /\ pc = "done"
  /\ \A i \in 1 .. (strLength - 1) :
       \/ inputString[i .. (strLength - 1)] @ inputString[0 .. (i - 1)]
          # inputString[bestOffset .. (strLength - 1)] @ inputString[0 .. (bestOffset - 1)]
       \/ i >= bestOffset

Termination == <>(pc = "done")

====