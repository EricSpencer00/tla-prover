---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet

\* The utility module defines zero-indexed sequences; here we work directly
\* with Seq(CharacterSet) so the model checker can enumerate over lengths.
VARIABLES inputString, strLen, failFcn, pIdx, loopCtr, bestOff, pc

TypeOK ==
  /\ inputString \in Seq(CharacterSet)
  /\ strLen = Len(inputString)
  /\ failFcn \in [0..(2 * strLen)] \cup {-1}
  /\ pIdx \in (-1)..(2 * strLen)
  /\ loopCtr \in (0..(2 * strLen))
  /\ bestOff \in 0..(strLen - 1)
  /\ pc \in {"outerCheck", "lookupFail", "innerLoop", "updateBest", "followFail", "postComp", "increment", "final"}

Init ==
  /\ inputString \in Seq(CharacterSet)
  /\ strLen' = Len(inputString)
  /\ failFcn' = -1
  /\ pIdx' = -1
  /\ loopCtr' = 1
  /\ bestOff' = 0
  /\ pc' = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopCtr < (2 * strLen) THEN pc' = "lookupFail" ELSE pc' = "final"
  /\ UNCHANGED <<inputString, strLen, failFcn, pIdx, loopCtr, bestOff>>

\* Lookup the failure function relative to the current candidate offset.
LookupFail ==
  /\ pc = "lookupFail"
  /\ failFcn' = IF failFcn # -1 THEN failFcn ELSE -1
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<inputString, strLen, pIdx, loopCtr, bestOff>>

\* Compare characters at the current loop position and candidate position.
InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET curChar == inputString[(loopCtr % strLen) + 1]
         candChar == inputString[((bestOff + loopCtr) % strLen) + 1]
     IN
       /\ IF curChar # candChar /\ pIdx # -1 THEN pc' = "innerLoop" ELSE pc' = "postComp"
       /\ IF curChar < candChar THEN bestOff' = loopCtr ELSE UNCHANGED bestOff
  /\ UNCHANGED <<inputString, strLen, failFcn, pIdx, loopCtr>>

\* Follow the failure function chain (shrinking the matched prefix).
FollowFail ==
  /\ pc = "postComp"
  /\ LET curChar == inputString[(loopCtr % strLen) + 1]
         candChar == inputString[((bestOff + loopCtr) % strLen) + 1]
     IN
       /\ IF curChar # candChar /\ pIdx = -1
            THEN bestOff' = IF curChar < candChar THEN loopCtr ELSE bestOff
            ELSE bestOff' = bestOff
       /\ failFcn' = IF curChar # candChar /\ pIdx = -1 THEN -1 ELSE pIdx + 1
       /\ pIdx' = IF curChar # candChar /\ pIdx = -1 THEN -1 ELSE pIdx
  /\ UNCHANGED <<inputString, strLen, loopCtr>>

Increment ==
  /\ pc = "postComp"
  /\ loopCtr' = loopCtr + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<inputString, strLen, failFcn, pIdx, bestOff>>

Final ==
  /\ pc = "final"
  /\ UNCHANGED <<inputString, strLen, failFcn, pIdx, loopCtr, bestOff, pc>>

Next ==
  \/ OuterCheck \/ LookupFail \/ InnerLoop \/ FollowFail \/ Increment \/ Final

Spec == Init /\ [][Next]_<<inputString, strLen, failFcn, pIdx, loopCtr, bestOff, pc>>

\* The best offset yields a lexicographically-minimal rotation: no other
\* rotation is strictly smaller, and ties only occur at larger offsets.
CandidateSequence ==
  \A i \in 1..strLen : inputString[(bestOff + i) % strLen + 1]

NoBetterRotation ==
  \A off \in 0..(strLen - 1) :
    LET seq == \A i \in 1..strLen : inputString[(off + i) % strLen + 1]
        diff == \E i \in 1..strLen :
          LET a == inputString[(bestOff + i) % strLen + 1]
              b == inputString[(off + i) % strLen + 1]
          IN a # b /\ a < b
    IN (seq = CandidateSequence) => (off >= bestOff)

TypeInvariant == TypeOK

Correctness == NoBetterRotation

Termination == <>(pc = "final")

====