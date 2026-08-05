---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet

ASSUME CharacterSet \subseteq Nat

VARIABLES inputString, stringLength, failureFunc, patternIdx, loopCounter, bestOffset, pc

vars == << inputString, stringLength, failureFunc, patternIdx, loopCounter, bestOffset, pc >>

Sentinel == 99

Corpus == UNION { CHARACTERSET ^ k : k \in {0, 1, 2, 3} }

TypeInvariant ==
  /\ inputString \in Corpus
  /\ stringLength = Len(inputString)
  /\ failureFunc \in [0..(2 * stringLength) -> {Sentinel} \union (0..(2 * stringLength))]
  /\ patternIdx \in {Sentinel} \union (0..(2 * stringLength))
  /\ loopCounter \in 0..(2 * stringLength)
  /\ bestOffset \in 0..(stringLength - 1)
  /\ pc \in {"outer", "lookup", "compare", "updateBest", "followFail", "post", "increment", "done"}

Init ==
  /\ inputString \in Corpus
  /\ stringLength = Len(inputString)
  /\ failureFunc = [i \in 0..(2 * Len(inputString)) |-> Sentinel]
  /\ patternIdx = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF loopCounter < 2 * stringLength THEN /\ pc' = "lookup"
                                         /\ UNCHANGED << inputString, stringLength, failureFunc, patternIdx, loopCounter, bestOffset >>
                           ELSE /\ pc' = "done"
                                /\ UNCHANGED << inputString, stringLength, failureFunc, patternIdx, loopCounter, bestOffset >>
  /\ UNCHANGED << >>

LookupFailure ==
  /\ pc = "lookup"
  /\ LET candidateIdx == (bestOffset + (IF patternIdx = Sentinel THEN 0 ELSE patternIdx)) % stringLength IN
     patternIdx' = failureFunc[candidateIdx]
  /\ pc' = "compare"
  /\ UNCHANGED << inputString, stringLength, failureFunc, loopCounter, bestOffset >>

CurrentChar == inputString[(loopCounter % stringLength) + 1]
CandidateChar == inputString[((bestOffset + (IF patternIdx = Sentinel THEN 0 ELSE patternIdx)) % stringLength) + 1]

CompareLoop ==
  /\ pc = "compare"
  /\ IF CurrentChar # CandidateChar /\ patternIdx # Sentinel
     THEN /\ pc' = "compare"
          /\ UNCHANGED << inputString, stringLength, failureFunc, patternIdx, loopCounter, bestOffset >>
     ELSE /\ pc' = "post"
          /\ UNCHANGED << inputString, stringLength, failureFunc, patternIdx, loopCounter, bestOffset >>

UpdateBest ==
  /\ pc = "compare"
  /\ CurrentChar < CandidateChar
  /\ patternIdx # Sentinel
  /\ bestOffset' = loopCounter % stringLength
  /\ pc' = "compare"
  /\ UNCHANGED << inputString, stringLength, failureFunc, patternIdx, loopCounter >>

FollowFailure ==
  /\ pc = "post"
  /\ patternIdx # Sentinel
  /\ patternIdx' = failureFunc[patternIdx]
  /\ pc' = "post"
  /\ UNCHANGED << inputString, stringLength, failureFunc, loopCounter, bestOffset >>

ResetOrExtend ==
  /\ pc = "post"
  /\ patternIdx = Sentinel
  /\ failureFunc' = [failureFunc EXCEPT ![patternIdx] = IF CurrentChar # CandidateChar THEN (IF CurrentChar < CandidateChar THEN Sentinel ELSE Sentinel) ELSE (IF patternIdx = Sentinel THEN Sentinel ELSE patternIdx + 1)]
  /\ bestOffset' = IF CurrentChar < CandidateChar THEN loopCounter % stringLength ELSE bestOffset
  /\ pc' = "increment"
  /\ UNCHANGED << inputString, stringLength, patternIdx, loopCounter >>

IncrementLoop ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outer"
  /\ UNCHANGED << inputString, stringLength, failureFunc, patternIdx, bestOffset >>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == OuterLoop \/ LookupFailure \/ CompareLoop \/ UpdateBest \/ FollowFailure \/ ResetOrExtend \/ IncrementLoop \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(LookupFailure) /\ WF_vars(CompareLoop) /\ WF_vars(UpdateBest) /\ WF_vars(FollowFailure) /\ WF_vars(ResetOrExtend) /\ WF_vars(IncrementLoop)

RotationAt(o) == inputString[(o % stringLength) + 1 .. stringLength] ^ inputString[1 .. (o % stringLength)]

Correctness == \A i \in 0..(stringLength - 1) : RotationAt(bestOffset) <= RotationAt(i)

Termination == <>(pc = "done")

====