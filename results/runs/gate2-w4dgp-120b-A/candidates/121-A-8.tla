---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS CharacterSet

VARIABLES inputString, strLength, failure, matchIdx, loopCounter, bestOffset, pc

vars == <<inputString, strLength, failure, matchIdx, loopCounter, bestOffset, pc>>

\* The algorithm runs over a doubled string (iterating up to twice the length)
\* to handle the circular wrap-around without explicit circular logic.
Twice == 2 * strLength
Sentinel == -1
MaxLen == 3

TypeInvariant ==
    /\ inputString \in [1..MaxLen -> CharacterSet]
    /\ strLength = Len(inputString)
    /\ failure \in [0..Twice -> Sentinel .. (Twice - 1)]
    /\ matchIdx \in Sentinel .. (Twice - 1)
    /\ loopCounter \in 1..Twice
    /\ bestOffset \in 0..(strLength - 1)
    /\ pc \in {"OuterCheck", "FailureLookup", "InnerLoop", "FailureFollow",
               "PostCompare", "Done"}

Init ==
    /\ \E s \in [1..MaxLen -> CharacterSet] : inputString = s
    /\ strLength = Len(inputString)
    /\ failure = [i \in 0..Twice |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "OuterCheck"

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF loopCounter < Twice
       THEN /\ pc' = "FailureLookup"
            /\ UNCHANGED <<inputString, strLength, failure, matchIdx,
                          loopCounter, bestOffset>>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<inputString, strLength, failure, matchIdx,
                          loopCounter, bestOffset>>
    /\ UNCHANGED <<inputString, strLength, failure, matchIdx,
                  loopCounter, bestOffset>>

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ matchIdx' = failure[loopCounter + bestOffset]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<inputString, strLength, failure, loopCounter, bestOffset>>

\* Indexing the circular string is done via the modulo operator.
InnerLoop ==
    /\ pc = "InnerLoop"
    /\ LET curChar == inputString[((loopCounter - 1) % strLength) + 1]
           candChar == inputString[((matchIdx + bestOffset) % strLength) + 1]
       IN /\ (curChar # candChar /\ matchIdx # Sentinel)
          \/ /\ curChar # candChar
             /\ matchIdx = Sentinel
    /\ pc' = "FailureFollow"
    /\ UNCHANGED <<inputString, strLength, failure, matchIdx,
                  loopCounter, bestOffset>>

FailureFollow ==
    /\ pc = "FailureFollow"
    /\ LET curChar == inputString[((loopCounter - 1) % strLength) + 1]
           candChar == inputString[((matchIdx + bestOffset) % strLength) + 1]
       IN /\ IF curChar < candChar
          THEN bestOffset' = loopCounter % strLength
          ELSE bestOffset' = bestOffset
    /\ matchIdx' = failure[loopCounter + bestOffset]
    /\ pc' = "PostCompare"
    /\ UNCHANGED <<inputString, strLength, failure, loopCounter>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ LET curChar == inputString[((loopCounter - 1) % strLength) + 1]
           candChar == inputString[((matchIdx + bestOffset) % strLength) + 1]
           newOffset == IF curChar < candChar
                         THEN loopCounter % strLength ELSE bestOffset
       IN /\ IF curChar # candChar /\ matchIdx = Sentinel
          THEN bestOffset' = newOffset
          ELSE bestOffset' = bestOffset
    /\ failure' = [failure EXCEPT ![loopCounter + bestOffset] =
                   IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1]
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "OuterCheck"
    /\ matchIdx' = Sentinel

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == OuterCheck \/ FailureLookup \/ InnerLoop \/ FailureFollow \/ PostCompare \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(FailureFollow) /\ WF_vars(PostCompare)

\* Upon termination the recorded offset yields the lexicographically-minimal
\* rotation of the input string (and the smallest such offset among ties).
\* The iteration explores every prefix of the doubled string, so the best
\* offset at the end must be better than every rotation that was examined.
Correctness ==
    \A i \in 1..strLength :
        LET cand == inputString[((bestOffset + i - 1) % strLength) + 1]
            rot(i) == [j \in 1..strLength |->
                          inputString[((bestOffset + i + j - 2) % strLength) + 1]]
            base == rot(1)
        IN \A k \in 1..strLength : rot(i)[k] >= base[k]

Terminating == (\A i \in 1..strLength : TRUE) ~> (pc = "Done")

====