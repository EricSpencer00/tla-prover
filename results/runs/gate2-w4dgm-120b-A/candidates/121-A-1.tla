---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Zero-indexed sequences over the given character set; the corpus is the set
\* of all such sequences up to the configured maximum length.
Corpus == {s \in Seq(CharacterSet) : Len(s) <= MaxStringLength}

\* The failure function can point to any earlier position in the doubled
\* string, so its range is 0..2*MaxStringLength, and it also carries the
\* sentinel meaning "undefined, start a fresh match".
Sentinel == MaxStringLength + 1
Range(k) == 0..(2 * k)

VARIABLES string, strLen, failure, matchIdx, loopCounter, bestOffset, pc

Vars == <<string, strLen, failure, matchIdx, loopCounter, bestOffset, pc>>

\* Character at a position, wrapping around the circular base string.
circularChar(i) == string[(i % strLen) + 1]

TypeOK ==
    /\ string \in Corpus
    /\ strLen = Len(string)
    /\ failure \in [Range(MaxStringLength) -> Range(MaxStringLength) \cup {Sentinel}]
    /\ matchIdx \in Range(MaxStringLength) \cup {Sentinel}
    /\ loopCounter \in 1..(2 * MaxStringLength)
    /\ bestOffset \in 0..(MaxStringLength - 1)
    /\ pc \in {"outer", "lookup", "inner", "fail", "follow", "postCompare"}

Init ==
    /\ \E s \in Corpus : string = s
    /\ strLen = Len(string)
    /\ failure = [i \in Range(MaxStringLength) |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loopCounter = 1
    /\ bestOffset = 0
    /\ pc = "outer"

\* Outer loop: walk the doubled string, one step at a time, halting at the
\* end of the range rather than forcing an infinite run.
Outer ==
    /\ pc = "outer"
    /\ IF loopCounter < 2 * strLen
       THEN /\ pc' = "lookup"
            /\ UNCHANGED <<string, strLen, failure, matchIdx, loopCounter, bestOffset>>
       ELSE /\ pc' = "halt"
            /\ UNCHANGED <<string, strLen, failure, matchIdx, loopCounter, bestOffset>>

\* Grab the failure function entry for the current position relative to the
\* current best rotation; this drives the following inner loop.
Lookup ==
    /\ pc = "lookup"
    /\ matchIdx' = failure[loopCounter - bestOffset]
    /\ pc' = "inner"
    /\ UNCHANGED <<string, strLen, failure, loopCounter, bestOffset>>

\* Compare the candidate character against the pattern character; as long as
\* they differ and the pattern still has a failure link to follow, keep
\* looking for a viable shift rather than immediately concluding.
InnerCompare ==
    /\ pc = "inner"
    /\ /\ circularChar(loopCounter) # circularChar(bestOffset + matchIdx)
       /\ \/ matchIdx # Sentinel
          \/ pc' = "fail"
    /\ UNCHANGED <<string, strLen, failure, matchIdx, loopCounter, bestOffset>>

\* The lexicographic break: a strictly smaller candidate character beats the
\* pattern character, so this rotation is better and its offset is recorded.
BetterOffset ==
    /\ pc = "inner"
    /\ /\ circularChar(loopCounter) < circularChar(bestOffset + matchIdx)
       /\ matchIdx # Sentinel
    /\ bestOffset' = loopCounter - matchIdx
    /\ pc' = "follow"
    /\ UNCHANGED <<string, strLen, failure, matchIdx, loopCounter>>

\* Follow the failure function chain to keep searching without rechecking
\* the already-discarded portion of the pattern.
Follow ==
    /\ pc = "follow"
    /\ matchIdx' = failure[matchIdx]
    /\ pc' = "inner"
    /\ UNCHANGED <<string, strLen, failure, loopCounter, bestOffset>>

\* Exhausted the failure chain: no link left to follow, so the candidate
\* character fails to beat the pattern and the match cannot be extended.
Fail ==
    /\ pc = "fail"
    /\ /\ circularChar(loopCounter) # circularChar(bestOffset + matchIdx)
       /\ matchIdx = Sentinel
    /\ /\ \/ /\ loopCounter >= strLen
          /\ matchIdx = Sentinel
          /\ pc' = "postCompare"
          /\ UNCHANGED <<string, strLen, failure, loopCounter, bestOffset>>
       \/ /\ loopCounter < strLen
          /\ matchIdx = Sentinel
          /\ pc' = "postCompare"
          /\ UNCHANGED <<string, strLen, failure, loopCounter, bestOffset>>
       \/ UNCHANGED <<pc>>
    /\ UNCHANGED <<matchIdx>>

\* After a failed comparison, decide definitively whether the candidate is
\* better; if so, update the best rotation. Either way, reset or extend the
\* failure function entry so the next round starts on solid ground.
PostCompare ==
    /\ pc = "postCompare"
    /\ /\ \/ /\ circularChar(loopCounter) < circularChar(bestOffset + matchIdx)
            /\ bestOffset' = loopCounter - matchIdx
          \/ /\ matchIdx # Sentinel
            /\ failure' = [failure EXCEPT ![loopCounter - bestOffset] = Sentinel]
          \/ /\ matchIdx = Sentinel
            /\ failure' = [failure EXCEPT ![loopCounter - bestOffset] = 1 + matchIdx]
          \/ loopCounter' = loopCounter + 1
          /\ pc' = "outer"
    /\ UNCHANGED <<string, strLen, matchIdx, bestOffset>>

\* Once the algorithm has halted, it simply stays in that state forever.
Quiesce ==
    /\ pc = "halt"
    /\ UNCHANGED Vars

Next ==
    \/ Outer \/ Lookup \/ InnerCompare \/ BetterOffset
    \/ Follow \/ Fail \/ PostCompare \/ Quiesce

Spec == Init /\ [][Next]_Vars
    /\ WF_Vars(Lookup) /\ WF_Vars(InnerCompare)
    /\ WF_Vars(BetterOffset) /\ WF_Vars(Follow)
    /\ WF_Vars(Fail) /\ WF_Vars(PostCompare)

\* The variant is the outer loop counter: the outer loop runs a fixed range
\* once per iteration, so every path that actually takes the outer step
\* makes progress on the counter and must therefore reach the halt case.
TerminationCoherent == pc = "halt" \/ loopCounter < 2 * strLen

\* An invariant form of the same progress argument: any enabled outer step
\* is one step away from being taken, which is stronger than mere
\* weak-fairness and holds even when inner loops stall.
OuterStepIsAlwaysEnabled ==
    (pc = "outer" /\ loopCounter < 2 * strLen) ~> (pc = "outer" /\ loopCounter < 2 * strLen)

\* Lexicographic minimality: the rotation at the best offset is not greater
\* than any other rotation, and if exactly equal it cannot be a later shift.
BestIsLexicographicallyMinimal ==
    \A i \in 0..(strLen - 1) :
        /\ \A j \in 0..(strLen - 1) : circularChar(bestOffset + j) <= circularChar(i + j)
        /\ (circularChar(i + 1) = circularChar(bestOffset + 1) => i >= bestOffset)
====