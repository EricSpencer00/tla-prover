---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet, Nat

\* sentinel means "undefined" for a failure-function entry
Sentinel == Nat

VARIABLES inputString, stringLength, failure, patIdx, loopCounter, bestOffset, pc

vars == <<inputString, stringLength, failure, patIdx, loopCounter, bestOffset, pc>>

\* All zero-indexed sequences over an alphabet that is a subset of Nat,
\* coupled with the empty sequence, form the corpus from which the input
\* string is nondeterministically chosen.
SeqOver(C) ==
  { s \in Seq(C) : \A i \in DOMAIN s : s[i] \in C }

TypeOK ==
  /\ inputString \in SeqOver(CharacterSet)
  /\ stringLength = Len(inputString)
  /\ failure \in [0 .. 2 * stringLength - 1 -> 0 .. Nat]
  /\ patIdx \in 0 .. Nat
  /\ loopCounter \in 1 .. 2 * stringLength
  /\ bestOffset \in 0 .. (IF stringLength > 0 THEN stringLength - 1 ELSE 0)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateOffset", "followChain",
             "postComp", "increment", "terminated"}

Init ==
  /\ inputString \in SeqOver(CharacterSet)
  /\ stringLength = Len(inputString)
  /\ failure = [i \in 0 .. 2 * stringLength - 1 |-> Sentinel]
  /\ patIdx = Sentinel
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCounter < 2 * stringLength THEN pc' = "lookup" ELSE pc' = "terminated"
  /\ UNCHANGED <<inputString, stringLength, failure, patIdx, loopCounter, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ patIdx' = failure[loopCounter - 1]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, stringLength, failure, loopCounter, bestOffset>>

CurrentChar(i) == inputString[(i % stringLength) + 1]
CandidateChar == CurrentChar(bestOffset + loopCounter)

InnerLoop ==
  /\ pc = "innerLoop"
  /\ IF patIdx # Sentinel /\ CurrentChar(loopCounter) # CandidateChar
       THEN pc' = "innerLoop"
       ELSE pc' = "postComp"
  /\ UNCHANGED <<inputString, stringLength, failure, patIdx, loopCounter, bestOffset>>

UpdateOffset ==
  /\ pc = "innerLoop"
  /\ patIdx # Sentinel
  /\ CurrentChar(loopCounter) < CandidateChar
  /\ bestOffset' = loopCounter
  /\ UNCHANGED <<inputString, stringLength, failure, patIdx, loopCounter, pc>>

FollowChain ==
  /\ pc = "innerLoop"
  /\ patIdx # Sentinel
  /\ patIdx' = failure[patIdx]
  /\ UNCHANGED <<inputString, stringLength, failure, loopCounter, bestOffset, pc>>

PostComp ==
  /\ pc = "postComp"
  /\ LET newOffset ==
        IF patIdx = Sentinel /\ CurrentChar(loopCounter) < CandidateChar
          THEN loopCounter
          ELSE bestOffset
     IN
     /\ bestOffset' = newOffset
     /\ failure' = [failure EXCEPT ![loopCounter - 1] =
                        IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
     /\ patIdx' = IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, stringLength, loopCounter>>

Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, stringLength, failure, patIdx, bestOffset>>

TerminationStall ==
  /\ pc = "terminated"
  /\ UNCHANGED vars

Next == OuterCheck \/ Lookup \/ InnerLoop \/ UpdateOffset \/ FollowChain
        \/ PostComp \/ Increment \/ TerminationStall

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(InnerLoop)

Rotate(s, k) == SubSeq(s, k, Len(s)) \o SubSeq(s, 1, k - 1)

AllRotations == { Rotate(inputString, k) : k \in 0 .. stringLength - 1 }

BestRotation == Rotate(inputString, bestOffset)

Correctness ==
  /\ BestRotation \in AllRotations
  /\ \A r \in AllRotations : BestRotation <= r
  /\ \A r \in AllRotations :
       (BestRotation = r) => (bestOffset <= Cardinality({ k \in 0 .. stringLength - 1 : Rotate(inputString, k) = r }))

Termination == <>(pc = "terminated")

TypeInvariant == TypeOK
====