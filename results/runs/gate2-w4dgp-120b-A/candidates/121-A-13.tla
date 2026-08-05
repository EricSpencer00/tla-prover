---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, ZSequences

(* Sequence indexing is zero-based throughout this module, via ZSequences. *)
ASSUME ZSequences.Nat = Nat

CONSTANTS CharacterSet

VARIABLES input, length, failureFunction, patternIndex, loopCounter, bestOffset, pc

vars == <<input, length, failureFunction, patternIndex, loopCounter, bestOffset, pc>>

Circular(i) == i % length
Sentinel == length
AllOffsets == 0 .. (length - 1)
Corpus == [ZSequences.Nat -> CharacterSet]

TypeInvariant ==
    /\ input \in Corpus
    /\ length = Len(input)
    /\ failureFunction \in [0 .. (2 * length) -> 0 .. length]
    /\ patternIndex \in 0 .. length
    /\ loopCounter \in 1 .. (2 * length)
    /\ bestOffset \in AllOffsets
    /\ pc \in {outerLoop, failLookup, innerLoop, updateOffset, followFailure, postCompare, increment, final}

Init ==
    /\ input \in Corpus
    /\ length = Len(input)
    /\ failureFunction = [i \in 0 .. (2 * length) |-> Sentinel]
    /\ patternIndex = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = outerLoop

OuterLoop ==
    /\ pc = outerLoop
    /\ IF loopCounter < (2 * length) THEN pc' = failLookup ELSE pc' = final
    /\ UNCHANGED <<input, length, failureFunction, patternIndex, loopCounter, bestOffset>>

FailLookup ==
    /\ pc = failLookup
    /\ patternIndex' = failureFunction[Circular(bestOffset + loopCounter)]
    /\ pc' = innerLoop
    /\ UNCHANGED <<input, length, failureFunction, loopCounter, bestOffset>>

InnerLoop ==
    /\ pc = innerLoop
    /\ (input[Circular(loopCounter)] # input[Circular(bestOffset + patternIndex)]) /\ patternIndex # Sentinel
        /\ pc' = innerLoop
    /\ ((input[Circular(loopCounter)] = input[Circular(bestOffset + patternIndex)]) \/ patternIndex = Sentinel)
        /\ pc' = postCompare
    /\ UNCHANGED <<input, length, failureFunction, patternIndex, loopCounter, bestOffset>>

UpdateOffset ==
    /\ pc = updateOffset
    /\ input[Circular(loopCounter)] < input[Circular(bestOffset + patternIndex)]
    /\ bestOffset' = loopCounter
    /\ pc' = followFailure
    /\ UNCHANGED <<input, length, failureFunction, patternIndex, loopCounter>>

FollowFailure ==
    /\ pc = followFailure
    /\ patternIndex' = failureFunction[patternIndex]
    /\ pc' = postCompare
    /\ UNCHANGED <<input, length, failureFunction, loopCounter, bestOffset>>

PostCompare ==
    /\ pc = postCompare
    /\ ((input[Circular(loopCounter)] # input[Circular(bestOffset + patternIndex)]) /\ patternIndex = Sentinel)
        /\ IF input[Circular(loopCounter)] < input[Circular(bestOffset + patternIndex)]
            THEN bestOffset' = loopCounter
            ELSE bestOffset' = bestOffset
    /\ IF input[Circular(loopCounter)] # input[Circular(bestOffset + patternIndex)]
        THEN failureFunction' = [failureFunction EXCEPT ![Circular(bestOffset + loopCounter)] = Sentinel]
        ELSE failureFunction' = [failureFunction EXCEPT ![Circular(bestOffset + loopCounter)] = patternIndex + 1]
    /\ pc' = increment
    /\ UNCHANGED <<input, length, patternIndex, loopCounter>>

Increment ==
    /\ pc = increment
    /\ loopCounter' = loopCounter + 1
    /\ pc' = outerLoop
    /\ UNCHANGED <<input, length, failureFunction, patternIndex, bestOffset>>

Stall ==
    /\ pc = final
    /\ UNCHANGED vars

Next == OuterLoop \/ FailLookup \/ InnerLoop \/ UpdateOffset \/ FollowFailure \/ PostCompare \/ Increment \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(FailLookup)
            /\ WF_vars(InnerLoop) /\ WF_vars(UpdateOffset) /\ WF_vars(FollowFailure)
            /\ WF_vars(PostCompare) /\ WF_vars(Increment) /\ WF_vars(Stall)

Terminated == pc = final

Correctness ==
    /\ Terminated
    /\ \A i \in AllOffsets : input[Circular(bestOffset)] <= input[Circular(i)]
    /\ \A i \in AllOffsets : (input[Circular(bestOffset)] = input[Circular(i)]) => (bestOffset <= i)

Properties == Terminated

====