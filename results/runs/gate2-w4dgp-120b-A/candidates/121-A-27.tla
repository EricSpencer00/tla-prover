---- MODULE LeastCircularSubstring ----
EXTENDS Integers, FiniteSets, Sequences, ZSequences

CONSTANTS
    CharacterSet

ASSUME CharacterSet \subseteq Nat

VARIABLES
    inputString, strLength, failureFunction, patternIndex, loopCounter, bestOffset, pc

vars == <<inputString, strLength, failureFunction, patternIndex, loopCounter, bestOffset, pc>>

Uninitialized == -1

LeftBound == 0
RightBound == 1

TypeOK ==
    /\ inputString \in UNION
         { [i \in 1 .. n |-> c] : n \in Nat /\ n >= 1 /\ n <= 3 /\ c \in CharacterSet }
    /\ strLength = Len(inputString)
    /\ failureFunction \in [0 .. 2 * strLength -> Uninitialized .. strLength]
    /\ patternIndex \in Uninitialized .. strLength
    /\ loopCounter \in 1 .. 2 * strLength
    /\ bestOffset \in 0 .. (strLength - 1)
    /\ pc \in { "outer_loop", "lookup_failure", "inner_compare", "follow_failure",
                "post_compare", "increment", "halted" }

Init ==
    /\ inputString \in UNION
         { [i \in 1 .. n |-> c] : n \in Nat /\ n >= 1 /\ n <= 3 /\ c \in CharacterSet }
    /\ strLength = Len(inputString)
    /\ failureFunction = [i \in 0 .. 2 * Len(inputString) |-> Uninitialized]
    /\ patternIndex = Uninitialized
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outer_loop"

OuterLoop ==
    /\ pc = "outer_loop"
    /\ IF loopCounter < 2 * strLength
       THEN /\ pc' = "lookup_failure"
            /\ UNCHANGED <<inputString, strLength, failureFunction, patternIndex, loopCounter, bestOffset>>
       ELSE /\ pc' = "halted"
            /\ UNCHANGED <<inputString, strLength, failureFunction, patternIndex, loopCounter, bestOffset>>

LookupFailure ==
    /\ pc = "lookup_failure"
    /\ patternIndex' = failureFunction[(loopCounter + bestOffset) % strLength]
    /\ pc' = "inner_compare"
    /\ UNCHANGED <<inputString, strLength, failureFunction, loopCounter, bestOffset>>

CurrentChar == inputString[(loopCounter % strLength) + 1]
CandidateChar(i) == inputString[((i + bestOffset) % strLength) + 1]

InnerCompare ==
    /\ pc = "inner_compare"
    /\ IF CurrentChar # CandidateChar(patternIndex) /\ patternIndex # Uninitialized
       THEN /\ pc' = "follow_failure"
            /\ UNCHANGED <<inputString, strLength, failureFunction, patternIndex, loopCounter, bestOffset>>
       ELSE /\ pc' = "post_compare"
            /\ UNCHANGED <<inputString, strLength, failureFunction, patternIndex, loopCounter, bestOffset>>

UpdateOnLess ==
    /\ CurrentChar < CandidateChar(patternIndex)
    /\ bestOffset' = loopCounter % strLength
    /\ UNCHANGED <<inputString, strLength, failureFunction, patternIndex, loopCounter, pc>>

FollowFailure ==
    /\ pc = "follow_failure"
    /\ patternIndex' = failureFunction[patternIndex]
    /\ pc' = "inner_compare"
    /\ UNCHANGED <<inputString, strLength, failureFunction, loopCounter, bestOffset>>

PostCompare ==
    /\ pc = "post_compare"
    /\ IF CurrentChar # CandidateChar(patternIndex) /\ patternIndex = Uninitialized
       THEN \/ /\ CurrentChar < CandidateChar(patternIndex)
               /\ bestOffset' = loopCounter % strLength
               \/ /\ bestOffset' = bestOffset
            /\ failureFunction' = [failureFunction EXCEPT ![(loopCounter + bestOffset) % strLength] = Uninitialized]
       ELSE /\ failureFunction' = [failureFunction EXCEPT ![(loopCounter + bestOffset) % strLength] = patternIndex + 1]
            /\ UNCHANGED bestOffset
    /\ UNCHANGED <<inputString, strLength, patternIndex, loopCounter, pc>>

Increment ==
    /\ pc = "increment"
    /\ loopCounter < 2 * strLength
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outer_loop"
    /\ UNCHANGED <<inputString, strLength, failureFunction, patternIndex, bestOffset>>

Stall ==
    /\ pc = "halted"
    /\ UNCHANGED vars

Next ==
    \/ OuterLoop
    \/ LookupFailure
    \/ InnerCompare
    \/ FollowFailure
    \/ PostCompare
    \/ Increment
    \/ Stall

Spec == Init /\ [][Next]_vars

LexicographicallyLeast ==
    /\ pc = "halted"
    /\ \A i \in 0 .. (strLength - 1) :
         LET candidate(i) == [k \in 1 .. strLength |-> inputString[((i + k) % strLength) + 1]] IN
         LET best == [k \in 1 .. strLength |-> inputString[((bestOffset + k) % strLength) + 1]] IN
         \/ \A k \in 1 .. strLength : best[k] < candidate(i)
            => True
            \/ (best[k] > candidate(i) => False)
            \/ (\A m \in 1 .. (k - 1) : best[m] = candidate(i)[m] /\ bestOffset <= i)

Termination == <>(pc = "halted")

====