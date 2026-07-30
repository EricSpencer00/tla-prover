---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet, Nat

\* Zero-indexed sequences are imported from a separate utility module; here
\* we use the built-in Sequences extension but treat every Seq as zero-indexed,
\* indexing with Modulo. The failure function is sized to twice the max string
\* length, so that the doubled string is covered without explicit wraparound.
Indices == 0..(Nat - 1)
Sentinel == Nat + 1
MaxDouble == 2 * Nat

VARIABLES inputString, length, failure, patIdx, loop, bestRot, pc
vars == <<inputString, length, failure, patIdx, loop, bestRot, pc>>

TypeOK ==
    /\ inputString \in Seq(CharacterSet)
    /\ length = Len(inputString)
    /\ failure \in [Indices \cup [0..MaxDouble] |-> 0..(Sentinel)]
    /\ patIdx \in 0..Sentinel
    /\ loop \in 1..MaxDouble
    /\ bestRot \in Indices
    /\ pc \in {"outerCheck", "failureLookup", "innerLoop",
               "updateBestLess", "followFailure", "postComp",
               "increment", "done"}

Init ==
    /\ \E s \in Seq(CharacterSet) : inputString' = s /\ length' = Len(s)
    /\ failure' = [i \in Indices \cup [0..MaxDouble] |-> Sentinel]
    /\ patIdx' = Sentinel
    /\ loop' = 1
    /\ bestRot' = 0
    /\ pc' = "outerCheck"

\* Outer loop runs until just below twice the string length.
OuterCheck ==
    /\ pc = "outerCheck"
    /\ IF loop < MaxDouble
       THEN pc' = "failureLookup"
       ELSE pc' = "done"
    /\ UNCHANGED <<inputString, length, failure, patIdx, loop, bestRot>>

FailureLookup ==
    /\ pc = "failureLookup"
    /\ patIdx' = failure[bestRot + loop - 1]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<inputString, length, failure, loop, bestRot>>

\* Compare the character at the loop position (modulo the length) with the
\* character at the candidate position derived from bestRot; continue the
\* inner loop while they differ and the failure chain is still non-empty.
InnerLoop ==
    /\ pc = "innerLoop"
    /\ LET cur == inputString[(loop % length) + 1]
           cand == inputString[((bestRot + loop) % length) + 1]
       IN IF cur # cand /\ patIdx # Sentinel
          THEN pc' = "updateBestLess"
          ELSE pc' = "postComp"
    /\ UNCHANGED <<inputString, length, failure, patIdx, loop, bestRot>>

\* If the current character is strictly better, update the best rotation.
UpdateBestLess ==
    /\ pc = "updateBestLess"
    /\ LET cur == inputString[(loop % length) + 1]
           cand == inputString[((bestRot + loop) % length) + 1]
       IN /\ cur < cand
          /\ bestRot' = loop % length
    /\ pc' = "followFailure"
    /\ UNCHANGED <<inputString, length, failure, patIdx, loop>>

\* Follow the failure function chain, equivalent to KMP's next step.
FollowFailure ==
    /\ pc = "followFailure"
    /\ patIdx' = failure[patIdx]
    /\ pc' = "innerLoop"
    /\ UNCHANGED <<inputString, length, failure, loop, bestRot>>

\* After the inner loop finishes, update the failure function entry.
PostComp ==
    /\ pc = "postComp"
    /\ LET cur == inputString[(loop % length) + 1]
           cand == inputString[((bestRot + loop) % length) + 1]
           newEntry == IF cur < cand THEN (patIdx + 1) % MaxDouble ELSE Sentinel
       IN /\ failure' = [failure EXCEPT ![bestRot + loop - 1] = newEntry]
          /\ bestRot' = IF cur < cand THEN loop % length ELSE bestRot
    /\ pc' = "increment"
    /\ UNCHANGED <<inputString, length, patIdx, loop>>

\* Increment the loop counter and return to the outer loop check.
Increment ==
    /\ pc = "increment"
    /\ loop' = loop + 1
    /\ pc' = "outerCheck"
    /\ UNCHANGED <<inputString, length, failure, patIdx, bestRot>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == OuterCheck \/ FailureLookup \/ InnerLoop \/ UpdateBestLess
        \/ FollowFailure \/ PostComp \/ Increment \/ Done

Spec == Init /\ [][Next]_vars
        /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup) /\ WF_vars(InnerLoop)
        /\ WF_vars(UpdateBestLess) /\ WF_vars(FollowFailure)
        /\ WF_vars(PostComp) /\ WF_vars(Increment)

\* Correctness: the best rotation is lexicographically minimal among all.
LexicographicallyLeast ==
    \A i \in Indices :
        LET rot(j) == inputString[((j + i) % length) + 1]
        IN rot(bestRot) <= rot(i)

TypeInvariant == TypeOK
Correctness == LexicographicallyLeast

Terminating == <>(pc = "done")
====