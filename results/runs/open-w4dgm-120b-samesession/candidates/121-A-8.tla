------------------------------ MODULE LeastCircularSubstring ------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet

StringLength == 3
Sentinel == 99
MaxLoops == StringLength * 2

VARIABLES inputString, strLen, failure, patIdx, loopCounter, bestOffset, pc
vars == <<inputString, strLen, failure, patIdx, loopCounter, bestOffset, pc>>

Corpus == UNION {[1..n -> CharacterSet] : n \in 1..StringLength}

TypeInvariant ==
    /\ inputString \in Corpus
    /\ strLen = Len(inputString)
    /\ failure \in [0..(strLen * 2) -> 0..(strLen * 2) \cup {Sentinel}]
    /\ patIdx \in 0..(strLen * 2) \cup {Sentinel}
    /\ loopCounter \in 0..MaxLoops
    /\ bestOffset \in 0..(strLen - 1)
    /\ pc \in {"outerCheck", "failureLookup", "innerCompare", "postCompare", "terminated"}

Init ==
    /\ \E s \in Corpus : inputString = s
    /\ strLen = Len(inputString)
    /\ failure = [i \in 0..(strLen * 2) |-> Sentinel]
    /\ patIdx = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outerCheck"

OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loopCounter < MaxLoops
       THEN pc' = "failureLookup"
       ELSE pc' = "terminated"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loopCounter, bestOffset>>

FailureLookup ==
    /\ pc = "failureLookup"
    /\ patIdx' = failure[loopCounter - bestOffset]
    /\ pc' = "innerCompare"
    /\ UNCHANGED <<inputString, strLen, failure, loopCounter, bestOffset>>

InnerCompare ==
    /\ pc = "innerCompare"
    /\ IF inputString[(loopCounter % strLen) + 1] = inputString[((loopCounter + patIdx) % strLen) + 1]
       THEN pc' = "postCompare"
       ELSE IF patIdx # Sentinel
            THEN pc' = "innerCompare"
            ELSE pc' = "postCompare"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loopCounter, bestOffset>>

UpdateBest ==
    /\ inputString[(loopCounter % strLen) + 1] < inputString[((loopCounter + patIdx) % strLen) + 1]
    /\ bestOffset' = loopCounter % strLen
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loopCounter, pc>>

ResetFailure ==
    /\ failure' = [failure EXCEPT ![loopCounter - bestOffset] = Sentinel]
    /\ UNCHANGED <<inputString, strLen, patIdx, loopCounter, bestOffset, pc>>

ExtendFailure ==
    /\ failure' = [failure EXCEPT ![loopCounter - bestOffset] = patIdx + 1]
    /\ UNCHANGED <<inputString, strLen, patIdx, loopCounter, bestOffset, pc>>

PostCompare ==
    /\ pc = "postCompare"
    /\ IF inputString[(loopCounter % strLen) + 1] # inputString[((loopCounter + patIdx) % strLen) + 1]
       THEN IF patIdx = Sentinel THEN UpdateBest /\ ExtendFailure ELSE ResetFailure
       ELSE pc' = "increment"
    /\ UNCHANGED <<inputString, strLen, patIdx, loopCounter, bestOffset>>

Increment ==
    /\ pc = "increment"
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, bestOffset>>

Stutter ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next == OuterCheck \/ FailureLookup \/ InnerCompare \/ PostCompare \/ Increment \/ Stutter

Spec == Init /\ [][Next]_vars

Correctness ==
    /\ \A i \in 0..(strLen - 1) :
         \A j \in 0..(strLen - 1) :
            \A k \in 0..(strLen - 1) :
                (LET s1 == [p \in 0..(strLen - 1) |-> inputString[((i + p) % strLen) + 1]]
                     s2 == [p \in 0..(strLen - 1) |-> inputString[((j + p) % strLen) + 1]]
                     s3 == [p \in 0..(strLen - 1) |-> inputString[((k + p) % strLen) + 1]]
                  IN
                    IF s1 = s2 THEN i <= j ELSE s1 < s2)
    /\ bestOffset = 0
    /\ \A j \in 0..(strLen - 1) :
         LET s1 == [p \in 0..(strLen - 1) |-> inputString[((bestOffset + p) % strLen) + 1]]
             s2 == [p \in 0..(strLen - 1) |-> inputString[((j + p) % strLen) + 1]]
         IN
           IF s1 = s2 THEN bestOffset <= j ELSE s1 < s2

Termination == <>(pc = "terminated")

=============================================================================