---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet

\* Zero-indexed strings are modeled as functions from domain indices to
\* characters, with Length tracking the highest index plus one.
Corpus == UNION { [1..n -> CharacterSet] : n \in (Nat \ {0}) }

VARIABLES inputStr, strLen, fail, patIdx, outerCnt, bestRot, pc

vars == <<inputStr, strLen, fail, patIdx, outerCnt, bestRot, pc>>

Sentinel == 0 - 1
MaxStrLen == 2
MaxIter == 2 * MaxStrLen

\* The algorithm's failure-function chain is exactly KMP's: each entry points
\* back to the longest border of the prefix ending there, and the loop
\* follows that chain whenever a comparison fails.
Init ==
    /\ inputStr \in Corpus
    /\ strLen = Len(inputStr)
    /\ fail = [i \in 0..MaxIter |-> Sentinel]
    /\ patIdx = Sentinel
    /\ outerCnt = 1
    /\ bestRot = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ outerCnt < MaxIter
    /\ pc' = "lookupFail"
    /\ UNCHANGED <<inputStr, strLen, fail, patIdx, outerCnt, bestRot>>

LookupFail ==
    /\ pc = "lookupFail"
    /\ fail' = [fail EXCEPT ![outerCnt] = fail[bestRot]]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputStr, strLen, patIdx, outerCnt, bestRot>>

Compare ==
    /\ pc = "compare"
    /\ LET curChar == inputStr[(outerCnt % strLen) + 1]
           candChar == inputStr[((bestRot + outerCnt) % strLen) + 1] IN
        /\ IF curChar # candChar /\ patIdx # Sentinel
           THEN pc' = "compare"
           ELSE pc' = "postCompare"
        /\ IF curChar < candChar /\ curChar # candChar /\ patIdx # Sentinel
           THEN bestRot' = outerCnt
           ELSE UNCHANGED bestRot
    /\ UNCHANGED <<inputStr, strLen, fail, patIdx, outerCnt>>

Follow ==
    /\ pc = "postCompare"
    /\ patIdx' = fail[patIdx]
    /\ pc' = "outerCheck"
    /\ outerCnt' = outerCnt + 1
    /\ UNCHANGED <<inputStr, strLen, fail, bestRot>>

PostCompare ==
    /\ pc = "postCompare"
    /\ LET curChar == inputStr[(outerCnt % strLen) + 1]
           candChar == inputStr[((bestRot + outerCnt) % strLen) + 1] IN
        /\ IF curChar # candChar /\ patIdx = Sentinel
           THEN bestRot' = IF curChar < candChar THEN outerCnt ELSE bestRot
           ELSE UNCHANGED bestRot
        /\ fail' = [fail EXCEPT ![outerCnt] =
             IF curChar # candChar /\ patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
    /\ UNCHANGED <<inputStr, strLen, patIdx, outerCnt, pc>>

Done ==
    /\ pc = "outerCheck"
    /\ outerCnt >= MaxIter
    /\ UNCHANGED vars

Stutter ==
    /\ pc = "outerCheck"
    /\ outerCnt >= MaxIter
    /\ UNCHANGED vars

Next == OuterCheck \/ LookupFail \/ Compare \/ Follow \/ PostCompare \/ Done \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Follow)

TypeInvariant ==
    /\ inputStr \in Corpus
    /\ strLen = Len(inputStr)
    /\ fail \in [0..MaxIter -> (0..MaxIter) \cup {Sentinel}]
    /\ patIdx \in (0..MaxIter) \cup {Sentinel}
    /\ outerCnt \in 0..MaxIter
    /\ bestRot \in 0..strLen

\* Correctness: the found rotation is lexicographically minimal among all
\* rotations. Ties are broken in favor of the smallest shift value.
Correctness ==
    \A s \in 0..(strLen - 1) : \A k \in 0..(strLen - 1) :
        LET r1 == [i \in 1..strLen |-> inputStr[((bestRot + i + s) % strLen) + 1]]
            r2 == [i \in 1..strLen |-> inputStr[((bestRot + i + k) % strLen) + 1]] IN
            \/ r1 <= r2
            \/ (r1 = r2 /\ s <= k)

Termination == <>(pc = "outerCheck" /\ outerCnt >= MaxIter)

====