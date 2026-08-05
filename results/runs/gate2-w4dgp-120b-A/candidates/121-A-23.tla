---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

VARIABLES inputString, stringLength, failureFunction, matchIndex, loopCounter, bestOffset, pc
vars == << inputString, stringLength, failureFunction, matchIndex, loopCounter, bestOffset, pc >>

Sentinel == 999
Corpus == UNION { [1..n -> CharacterSet] : n \in Nat }

Init ==
    /\ inputString \in Corpus
    /\ stringLength = Len(inputString)
    /\ failureFunction \in [0..(2 * stringLength) -> 0..(2 * stringLength) \cup {Sentinel}]
    /\ \A i \in 0..(2 * stringLength) : failureFunction[i] = Sentinel
    /\ matchIndex = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outer"

OuterCheck ==
    /\ pc = "outer"
    /\ IF loopCounter < (2 * stringLength)
       THEN /\ pc' = "lookup"
            /\ UNCHANGED << inputString, stringLength, failureFunction, matchIndex, loopCounter, bestOffset >>
       ELSE /\ pc' = "done"
            /\ UNCHANGED << inputString, stringLength, failureFunction, matchIndex, loopCounter, bestOffset >>

Lookup ==
    /\ pc = "lookup"
    /\ matchIndex' = failureFunction[loopCounter - bestOffset]
    /\ pc' = "compare"
    /\ UNCHANGED << inputString, stringLength, failureFunction, loopCounter, bestOffset >>

CharAt(i) == inputString[(i % stringLength) + 1]
Candidate == CharAt(bestOffset + (matchIndex + 1))

CompareLoop ==
    /\ pc = "compare"
    /\ CharAt(loopCounter) # Candidate
    /\ matchIndex # Sentinel
    /\ pc' = "compare"
    /\ UNCHANGED << inputString, stringLength, failureFunction, matchIndex, loopCounter, bestOffset >>

UpdateBestLess ==
    /\ CharAt(loopCounter) < Candidate
    /\ bestOffset' = loopCounter - (matchIndex + 1)
    /\ UNCHANGED << inputString, stringLength, failureFunction, matchIndex, loopCounter, pc >>

FollowFailure ==
    /\ matchIndex # Sentinel
    /\ matchIndex' = failureFunction[matchIndex]
    /\ UNCHANGED << inputString, stringLength, failureFunction, loopCounter, bestOffset, pc >>

PostCompare ==
    /\ pc = "compare"
    /\ \/ (CharAt(loopCounter) # Candidate /\ matchIndex = Sentinel)
       \/ (pc = "compare" /\ (CharAt(loopCounter) # Candidate \/ matchIndex = Sentinel))
    /\ IF CharAt(loopCounter) < Candidate
       THEN bestOffset' = loopCounter - (matchIndex + 1)
       ELSE bestOffset' = bestOffset
    /\ failureFunction' = [failureFunction EXCEPT ![loopCounter] = IF matchIndex = Sentinel THEN Sentinel ELSE matchIndex + 1]
    /\ pc' = "increment"
    /\ UNCHANGED << inputString, stringLength, matchIndex, loopCounter >>

Increment ==
    /\ pc = "increment"
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outer"
    /\ UNCHANGED << inputString, stringLength, failureFunction, matchIndex, bestOffset >>

Done == pc = "done"

Stall ==
    /\ Done
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ Lookup \/ CompareLoop \/ UpdateBestLess \/ FollowFailure \/ PostCompare \/ Increment \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(CompareLoop) /\ WF_vars(PostCompare) /\ WF_vars(Increment)

TypeInvariant ==
    /\ inputString \in Corpus
    /\ stringLength = Len(inputString)
    /\ failureFunction \in [0..(2 * stringLength) -> 0..(2 * stringLength) \cup {Sentinel}]
    /\ matchIndex \in 0..(2 * stringLength) \cup {Sentinel}
    /\ loopCounter \in 0..(2 * stringLength)
    /\ bestOffset \in 0..(stringLength - 1)

LexicographicallyLessOrEqual(s1, s2) ==
    \A i \in 0..(stringLength - 1) :
        LET a == s1[(i % stringLength) + 1]
            b == s2[(i % stringLength) + 1]
        IN (a < b) \/ (a = b)

Correctness ==
    /\ ~Done
       => (bestOffset \in 0..(stringLength - 1))
    /\ Done
       => /\ \A o \in 0..(stringLength - 1) : LexicographicallyLessOrEqual(
                [i \in 1..stringLength |-> CharAt(bestOffset + i)],
                [i \in 1..stringLength |-> CharAt(o + i)])
          /\ (\A o \in 0..(stringLength - 1) :
                LexicographicallyLessOrEqual(
                    [i \in 1..stringLength |-> CharAt(bestOffset + i)],
                    [i \in 1..stringLength |-> CharAt(o + i)])
                => bestOffset <= o)

Termination == <>Done

====