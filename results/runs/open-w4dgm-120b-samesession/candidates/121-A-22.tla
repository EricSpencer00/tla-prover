---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Replaces the standard Nat with a finite version, so the model stays
\* finite while keeping the usual arithmetic operators.
Nat == CharacterSet

VARIABLES string, length, failure, patternIndex, offset, loopCounter, pc

vars == <<string, length, failure, patternIndex, offset, loopCounter, pc>>

Sentinel == length

TypeInvariant ==
  /\ string \in Seq(CharacterSet)
  /\ length = Len(string)
  /\ failure \in [0 .. 2 * length -> 0 .. length]
  /\ patternIndex \in 0 .. length
  /\ offset \in 0 .. length - 1
  /\ loopCounter \in 0 .. 2 * length
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "update", "follow", "postCompare", "increment", "done"}

\* A rotation is a contiguous subsequence of the doubled string; the empty
\* string is its own smallest rotation.
Rotation(i) == SubSeq(string, i, i + length - 1)

LexAtMost(i, j) == Rotation(i) # {} => Rotation(i) <= Rotation(j)

Init ==
  /\ \E s \in [1 .. Nat] -> Seq(CharacterSet:
       /\ Len(s) <= Nat
       /\ string' = s
       /\ length' = Len(s)
       /\ failure' = [k \in 0 .. 2 * Nat |-> Sentinel]
       /\ patternIndex' = Sentinel
       /\ offset' = 0
       /\ loopCounter' = 1
       /\ pc' = "outerCheck"

LookupFailure ==
  /\ pc = "outerCheck"
  /\ loopCounter < 2 * length
  /\ failure' = [failure EXCEPT ![loopCounter] = failure[loopCounter]]
  /\ pc' = "lookup"
  /\ UNCHANGED <<string, length, patternIndex, offset, loopCounter>>

InnerLoop ==
  /\ pc = "lookup"
  /\ IF \E i \in 0 .. length - 1 :
       /\ string[(loopCounter + i) % length] # string[(offset + i) % length]
       /\ patternIndex # Sentinel
       /\ i >= patternIndex
     THEN pc' = "innerLoop"
     ELSE pc' = "postCompare"
  /\ UNCHANGED <<string, length, failure, patternIndex, offset, loopCounter>>

UpdateOffset ==
  /\ pc = "innerLoop"
  /\ LET i == CHOOSE i \in 0 .. length - 1 :
        /\ string[(loopCounter + i) % length] # string[(offset + i) % length]
        /\ patternIndex # Sentinel
        /\ i >= patternIndex
  / string[(loopCounter + i) % length] < string[(offset + i) % length]
  /\ offset' = loopCounter % length
  /\ pc' = "follow"
  /\ UNCHANGED <<string, length, failure, patternIndex, loopCounter>>

FollowChain ==
  /\ pc = "follow"
  /\ patternIndex' = failure[loopCounter]
  /\ pc' = "postCompare"
  /\ UNCHANGED <<string, length, failure, offset, loopCounter>>

PostCompare ==
  /\ pc = "postCompare"
  /\ LET i == CHOOSE i \in 0 .. length - 1 :
        /\ string[(loopCounter + i) % length] # string[(offset + i) % length]
        /\ (patternIndex = Sentinel \/ i < patternIndex)
     IN
     /\ IF string[(loopCounter + i) % length] < string[(offset + i) % length]
        THEN offset' = loopCounter % length
        ELSE offset' = offset
     /\ failure' = [failure EXCEPT ![loopCounter] =
           IF patternIndex = Sentinel THEN Sentinel ELSE patternIndex + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<string, length, patternIndex, loopCounter>>

Increment ==
  /\ pc = "increment"
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<string, length, failure, patternIndex, offset>>

Done ==
  /\ pc = "outerCheck"
  /\ loopCounter >= 2 * length
  /\ pc' = "done"
  /\ UNCHANGED <<string, length, failure, patternIndex, offset, loopCounter>>

Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ LookupFailure
  \/ InnerLoop
  \/ UpdateOffset
  \/ FollowChain
  \/ PostCompare
  \/ Increment
  \/ Done
  \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(LookupFailure) /\ WF_vars(Increment)

Correctness ==
  /\ \A i \in 0 .. length - 1 : LexAtMost(i, offset)
  /\ \A i \in 0 .. length - 1 :
       Rotation(i) = Rotation(offset) => i >= offset

Termination == <>(pc = "done")

====