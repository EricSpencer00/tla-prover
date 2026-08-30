------------------------- MODULE LeastCircularSubstring -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

VARIABLES inputString, stringLen, failure, patternIndex, loopCounter, bestOffset, pc

vars == <<inputString, stringLen, failure, patternIndex, loopCounter, bestOffset, pc>>

TypeInvariant ==
    /\ inputString \in Seq(CharacterSet)
    /\ stringLen = Len(inputString)
    /\ failure \in [0..2*stringLen -> 0..stringLen \cup {stringLen}]
    /\ patternIndex \in 0..stringLen
    /\ loopCounter \in 0..2*stringLen
    /\ bestOffset \in 1..stringLen
    /\ pc \in {"outerCheck", "lookup", "compare", "update", "followLink", "postCompare", "final"}

Init ==
    /\ inputString \in Seq(CharacterSet)
    /\ stringLen = Len(inputString)
    /\ failure = [i \in 0..2*stringLen |-> stringLen]
    /\ patternIndex = stringLen
    /\ loopCounter = 1
    /\ bestOffset = 1
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCounter < 2 * stringLen
       THEN pc' = "lookup"
       ELSE pc' = "final"
    /\ UNCHANGED <<inputString, stringLen, failure, patternIndex, loopCounter, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ patternIndex' = failure[loopCounter % stringLen]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, stringLen, failure, loopCounter, bestOffset>>

Compare ==
    /\ pc = "compare"
    /\ IF (inputString[(loopCounter + patternIndex) % stringLen] # inputString[(bestOffset + patternIndex) % stringLen])
          /\ patternIndex # stringLen
       THEN pc' = "followLink"
       ELSE pc' = "postCompare"
    /\ UNCHANGED <<inputString, stringLen, failure, patternIndex, loopCounter, bestOffset>>

Update ==
    /\ pc = "update"
    /\ inputString[(loopCounter + patternIndex) % stringLen] < inputString[(bestOffset + patternIndex) % stringLen]
    /\ bestOffset' = loopCounter % stringLen
    /\ pc' = "followLink"
    /\ UNCHANGED <<inputString, stringLen, failure, patternIndex, loopCounter>>

FollowLink ==
    /\ pc = "followLink"
    /\ patternIndex' = failure[patternIndex]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, stringLen, failure, loopCounter, bestOffset>>

PostCompare ==
    /\ pc = "postCompare"
    /\ \/ (inputString[(loopCounter + patternIndex) % stringLen] # inputString[(bestOffset + patternIndex) % stringLen])
            /\ patternIndex = stringLen
            /\ inputString[(loopCounter + patternIndex) % stringLen] < inputString[(bestOffset + patternIndex) % stringLen]
            /\ bestOffset' = loopCounter % stringLen
            /\ failure' = [failure EXCEPT ![loopCounter] = stringLen]
       \/ (inputString[(loopCounter + patternIndex) % stringLen] # inputString[(bestOffset + patternIndex) % stringLen])
            /\ patternIndex = stringLen
            /\ inputString[(loopCounter + patternIndex) % stringLen] = inputString[(bestOffset + patternIndex) % stringLen]
            /\ failure' = [failure EXCEPT ![loopCounter] = patternIndex + 1]
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, stringLen, patternIndex, bestOffset>>

Final ==
    /\ pc = "final"
    /\ pc' = pc
    /\ UNCHANGED vars

Next == OuterCheck \/ Lookup \/ Compare \/ Update \/ FollowLink \/ PostCompare \/ Final

Spec == Init /\ [][Next]_vars /\ SF_vars(Final)

LessSeq(p, q) ==
    LET n == Len(p) IN
    \E k \in 1..n : \A i \in 1..n : (p[(i + k) % n] < q[(i + k) % n])
                        \/ (p[(i + k) % n] = q[(i + k) % n] /\ i = n)

SameSeq(p, q) ==
    LET n == Len(p) IN
    \E k \in 1..n : \A i \in 1..n : p[(i + k) % n] = q[(i + k) % n]

Correctness ==
    /\ \A i \in 1..stringLen : ~LessSeq(inputString, RotateLeft(inputString, i))
    /\ \A i \in 1..stringLen : (SameSeq(inputString, RotateLeft(inputString, i)) => bestOffset <= i)

Termination == []<>(pc = "final")
=============================================================================