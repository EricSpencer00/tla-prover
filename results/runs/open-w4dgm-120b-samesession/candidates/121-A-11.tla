--------------------------- MODULE LeastCircularSubstring ---------------------------
EXTENDS Naturals, FiniteSets, ZSequences

CONSTANTS CharacterSet

ASSUME IsFiniteSet(CharacterSet)

VARIABLES inputString, length, failure, patIdx, loopCounter, bestOffset, pc
vars == <<inputString, length, failure, patIdx, loopCounter, bestOffset, pc>>

MAXL == 3
UNKNOWN == MAXL + 1

Corpus == { s \in Seq(CharacterSet) : Len(s) <= MAXL }

Init0(x) == IF x \in Corpus /\ Length(x) > 0 THEN x ELSE CHOOSE y \in Corpus : Length(y) > 0

Init ==
    /\ inputString' = Init0(CHOOSE s \in Corpus : TRUE)
    /\ length' = Length(inputString')
    /\ failure = [k \in 0..(2 * MAXL) |-> UNKNOWN]
    /\ patIdx' = UNKNOWN
    /\ loopCounter' = 1
    /\ bestOffset' = 0
    /\ pc' = "outerCheck"

CharAt(i) == inputString'[(i % length) + 1]

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCounter < 2 * length
         THEN /\ pc' = "lookup"
              /\ UNCHANGED <<inputString, length, failure, patIdx, loopCounter, bestOffset>>
         ELSE /\ pc' = "done"
              /\ UNCHANGED <<inputString, length, failure, patIdx, loopCounter, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ failure' = [failure EXCEPT ![loopCounter] = failure[bestOffset]]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, length, patIdx, loopCounter, bestOffset>>

Compare ==
    /\ pc = "compare"
    /\ IF CharAt(loopCounter) # CharAt(bestOffset + loopCounter)
         THEN /\ patIdx' = failure[loopCounter]
              /\ pc' = IF patIdx = UNKNOWN THEN "postCompare" ELSE "compare"
         ELSE /\ pc' = "postCompare"
    /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset>>

PotentialUpdate ==
    /\ pc = "compare"
    /\ CharAt(loopCounter) < CharAt(bestOffset + loopCounter)
    /\ patIdx # UNKNOWN
    /\ bestOffset' = loopCounter
    /\ UNCHANGED <<inputString, length, failure, patIdx, loopCounter, pc>>

FollowFailure ==
    /\ pc = "compare"
    /\ patIdx # UNKNOWN
    /\ patIdx' = failure[patIdx]
    /\ UNCHANGED <<inputString, length, failure, loopCounter, bestOffset, pc>>

PostCompare ==
    /\ pc = "postCompare"
    /\ IF CharAt(loopCounter) < CharAt(bestOffset + loopCounter)
         THEN bestOffset' = loopCounter
         ELSE bestOffset' = bestOffset
    /\ failure' = [failure EXCEPT ![loopCounter] = IF patIdx = UNKNOWN THEN UNKNOWN ELSE patIdx + 1]
    /\ pc' = "advance"
    /\ UNCHANGED <<inputString, length, patIdx, loopCounter>>

Advance ==
    /\ pc = "advance"
    /\ loopCounter' = loopCounter + 1
    /\ patIdx' = UNKNOWN
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, length, failure, bestOffset>>

Stutter ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ Lookup \/ Compare \/ PotentialUpdate
    \/ FollowFailure \/ PostCompare \/ Advance \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup) /\ WF_vars(Compare)
        /\ WF_vars(PostCompare) /\ WF_vars(Advance)

TypeInvariant ==
    /\ inputString \in Corpus
    /\ length = Len(inputString)
    /\ failure \in [0..(2 * MAXL) -> 0..(MAXL + 1)]
    /\ patIdx \in 0..(MAXL + 1)
    /\ loopCounter \in 0..(2 * MAXL)
    /\ bestOffset \in 0..(MAXL - 1)
    /\ pc \in {"outerCheck", "lookup", "compare", "postCompare", "advance", "done"}

Correctness ==
    /\ \A i \in 0..(length - 1) : \A j \in 0..(length - 1) :
         \A k \in 1..length :
            ( \A m \in 0..(k - 1) : CharAt(i + m) = CharAt(j + m) )
              => (CharAt(i + k) <= CharAt(j + k))
    /\ \A i \in 0..(length - 1) : CharAt(i + bestOffset) = CharAt(bestOffset)

Termination == (pc # "done") ~> (pc = "done")
================================================================================