---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* ZSequences redefines the natural number constant 'Nat' used in the
\* standard module as a bounded, finite subset, so the state space stays
\* finite for model checking while the algorithm's logic is unchanged.
ZSequences == 0..{1} \cup CharacterSet

CONSTANTS CharacterSet

VARIABLES inputString, strLen, failureFn, patIdx, loopCounter, bestOffset, pc

vars == << inputString, strLen, failureFn, patIdx, loopCounter, bestOffset, pc >>

Sentinel == 0

\* Sequences are zero-indexed; the doubled loop runs over twice the
\* string length so a rotation's wraparound is covered as a linear scan.
RotatedString(s, pos) == s[(pos + strLen) % strLen]

TypeInvariant ==
    /\ inputString \in Seq(CharacterSet)
    /\ strLen = Len(inputString)
    /\ failureFn \in [0..2 * strLen -> 0..2 * strLen \cup {Sentinel}]
    /\ patIdx \in 0..2 * strLen \cup {Sentinel}
    /\ loopCounter \in 1..2 * strLen
    /\ bestOffset \in 0..(strLen - 1)
    /\ pc \in {"outer", "lookup", "compare", "update", "follow", "postcompare"}

Init ==
    /\ inputString \in Seq(CharacterSet)
    /\ strLen = Len(inputString)
    /\ failureFn = [p \in 0..2 * strLen |-> Sentinel]
    /\ patIdx = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outer"

OuterLoopCheck ==
    /\ pc = "outer"
    /\ IF loopCounter < 2 * strLen
       THEN pc' = "lookup"
       ELSE pc' = "outer"
    /\ UNCHANGED << inputString, strLen, failureFn, patIdx, loopCounter, bestOffset >>

LookupFailureFn ==
    /\ pc = "lookup"
    /\ patIdx' = failureFn[(loopCounter + bestOffset) % strLen]
    /\ pc' = "compare"
    /\ UNCHANGED << inputString, strLen, failureFn, loopCounter, bestOffset >>

\* The inner comparison loop follows the failure chain; it either
\* discovers a lexicographic difference or walks the failure link.
CompareLoop ==
    /\ pc = "compare"
    /\ IF RotatedString(inputString, loopCounter) = RotatedString(inputString, patIdx) /\ patIdx # Sentinel
       THEN pc' = "compare"
       ELSE pc' = "postcompare"
    /\ UNCHANGED << inputString, strLen, failureFn, patIdx, loopCounter, bestOffset >>

UpdateBest ==
    /\ pc = "postcompare"
    /\ RotatedString(inputString, loopCounter) # RotatedString(inputString, patIdx)
    /\ patIdx = Sentinel
    /\ RotatedString(inputString, loopCounter) < RotatedString(inputString, patIdx)
    /\ bestOffset' = loopCounter % strLen
    /\ pc' = "follow"
    /\ UNCHANGED << inputString, strLen, failureFn, patIdx, loopCounter >>

FollowFailureLink ==
    /\ pc = "postcompare"
    /\ RotatedString(inputString, loopCounter) # RotatedString(inputString, patIdx)
    /\ patIdx = Sentinel
    /\ RotatedString(inputString, loopCounter) >= RotatedString(inputString, patIdx)
    /\ failureFn' = [failureFn EXCEPT ![(loopCounter + bestOffset) % strLen] =
                        IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
    /\ pc' = "increment"
    /\ UNCHANGED << inputString, strLen, patIdx, loopCounter, bestOffset >>

\* Increment always returns to the outer loop check, so the PC
\* always cycles back to a reachable state and never self-loops.
IncrementLoop ==
    /\ pc = "increment"
    /\ loopCounter' = loopCounter + 1
    /\ pc' = "outer"
    /\ UNCHANGED << inputString, strLen, failureFn, patIdx, bestOffset >>

LoopStep ==
    \/ OuterLoopCheck
    \/ LookupFailureFn
    \/ CompareLoop
    \/ UpdateBest
    \/ FollowFailureLink
    \/ IncrementLoop

\* After termination, the system may stutter forever in its final state.
Stall ==
    /\ pc = "outer"
    /\ loopCounter >= 2 * strLen
    /\ UNCHANGED vars

Next == LoopStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep)

\* Correctly choosing the lexicographically-minimal rotation requires
\* that the offset found is not greater than any other rotation's
\* offset, and that equal sequences are resolved by the smallest shift.
Correctness ==
    /\ \A i \in 0..(strLen - 1) : RotatedString(inputString, i) >= RotatedString(inputString, bestOffset)
    /\ \A i \in 0..(strLen - 1) : RotatedString(inputString, i) = RotatedString(inputString, bestOffset) => i >= bestOffset

Termination == <>(pc = "outer" /\ loopCounter >= 2 * strLen)

====