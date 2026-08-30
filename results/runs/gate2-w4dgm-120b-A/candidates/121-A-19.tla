---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

Sentinel == 9999

VARIABLES inputString, strLength, failure, patternIndex, loopCounter, bestOffset, pc

vars == <<inputString, strLength, failure, patternIndex, loopCounter, bestOffset, pc>>

Corpus == [n \in 0..(strLength - 1) |-> inputString[n]]

TypeInvariant ==
    /\ inputString \in Seq(CharacterSet)
    /\ strLength = Len(inputString)
    /\ failure \in [0..(2 * strLength) -> 0..(2 * strLength) \cup {Sentinel}]
    /\ patternIndex \in 0..(2 * strLength) \cup {Sentinel}
    /\ loopCounter \in 0..(2 * strLength)
    /\ bestOffset \in 0..(strLength - 1)
    /\ pc \in {"outerCheck", "lookup", "compare", "update", "follow", "postCompare", "final"}

Init ==
    /\ \E seq \in Seq(CharacterSet) : inputString = seq
    /\ strLength = Len(inputString)
    /\ failure = [n \in 0..(2 * strLength) |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

Rotation(n) == SubSeq(Corpus, n, n + strLength - 1)

Compare(a, b) ==
    IF a < b THEN "lt"
    ELSE IF a > b THEN "gt"
    ELSE "eq"

\* 1. Outer loop: drive the doubled-index scan around the circular string.
OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCounter < 2 * strLength
         THEN pc' = "lookup"
         ELSE pc' = "final"
    /\ UNCHANGED <<inputString, strLength, failure, patternIndex, loopCounter, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ failure' = [failure EXCEPT ![loopCounter] = failure[bestOffset]]
    /\ patternIndex' = failure[bestOffset]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, strLength, loopCounter, bestOffset>>

\* 2. Inner loop: compare the character at the scan position with the one at
\* the candidate rotation offset, advancing the pattern index on mismatch.
CompareStep ==
    /\ pc = "compare"
    /\ LET curChar == Corpus[loopCounter]
           candChar == Corpus[loopCounter + patternIndex]
       IN \/ (curChar # candChar /\ patternIndex # Sentinel)
             => pc' = "compare"
          \/ (curChar = candChar \/ patternIndex = Sentinel)
             => pc' = "postCompare"
    /\ UNCHANGED <<inputString, strLength, failure, patternIndex, loopCounter, bestOffset>>

UpdateBest ==
    /\ pc = "compare"
    /\ LET curChar == Corpus[loopCounter]
           candChar == Corpus[loopCounter + patternIndex]
       IN curChar < candChar
          => bestOffset' = loopCounter
          /\ UNCHANGED <<inputString, strLength, failure, patternIndex, loopCounter, pc>>
    /\ UNCHANGED <<inputString, strLength, failure, patternIndex, loopCounter, bestOffset>>

FollowFailure ==
    /\ pc = "compare"
    /\ patternIndex # Sentinel
    /\ patternIndex' = failure[patternIndex]
    /\ pc' = "compare"
    /\ UNCHANGED <<inputString, strLength, failure, loopCounter, bestOffset>>

\* 3. After the inner loop exits, set the failure function so the next start is
\* always anchored on a maximal proper border of the current best rotation.
PostCompare ==
    /\ pc = "postCompare"
    /\ LET curChar == Corpus[loopCounter]
           candChar == Corpus[loopCounter + patternIndex]
       IN /\ IF curChar # candChar /\ patternIndex = Sentinel
                THEN IF curChar < candChar
                        THEN bestOffset' = loopCounter
                        ELSE UNCHANGED bestOffset
                /\ failure' = [failure EXCEPT ![loopCounter] = Sentinel]
                /\ UNCHANGED <<inputString, strLength, patternIndex, loopCounter>>
             /\ IF curChar # candChar /\ patternIndex # Sentinel
                THEN failure' = [failure EXCEPT ![loopCounter] = patternIndex + 1]
                /\ UNCHANGED <<inputString, strLength, patternIndex, loopCounter, bestOffset>>
             /\ IF curChar = candChar
                THEN UNCHANGED <<inputString, strLength, failure, patternIndex, loopCounter bestOffset>>
    /\ pc' = "incrementCounter"
    /\ UNCHANGED <<patternIndex>>

IncrementCounter ==
    /\ pc = "incrementCounter"
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, strLength, failure, patternIndex, bestOffset>>

\* 4. A stuttering final action keeps the model alive once the algorithm has
\* terminated at its final state.
Final ==
    /\ pc = "final"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ CompareStep
    \/ UpdateBest
    \/ FollowFailure
    \/ PostCompare
    \/ IncrementCounter
    \/ Final

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck)

\* Lexicographic minimality of the best rotation, plus smallest index on ties.
Correctness ==
    /\ \A k \in 0..(strLength - 1) : Compare(Rotation(bestOffset), Rotation(k)) \in {"lt", "eq"}
    /\ \A k \in 0..(strLength - 1) :
         (Compare(Rotation(bestOffset), Rotation(k)) = "eq") => (bestOffset <= k)

Termination == <>(pc = "final")

====