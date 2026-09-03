---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* A nondeterministic input string over a finite character set; the algorithm
\* computes the lexicographically smallest rotation of this circular string.
CharacterSet == 0..1

[ZSequences]CharacterSet == CharacterSet

VARIABLES input, slen, failure, patIdx, loopIdx, bestOffset, pc

vars == <<input, slen, failure, patIdx, loopIdx, bestOffset, pc>>

Sentinel == 0 - 1
MaxLen == 2
MaxLoop == 2 * MaxLen - 1

InRange(i, n) == i >= 0 /\ i < n

\* Weaker type invariant (bounds only) -- the lexicographic correctness
\* property below is the substance; no bound here can replace it.
TypeInvariant ==
    /\ input \in (CharacterSet)^MaxLen /\ slen = Len(input)
    /\ failure \in [0..(2 * MaxLen) -> (Sentinel..(2 * MaxLen))]
    /\ patIdx \in (Sentinel..(2 * MaxLen)) /\ loopIdx \in 0..MaxLoop
    /\ bestOffset \in 0..(MaxLen - 1)

Init ==
    /\ \E s \in (CharacterSet)^MaxLen : input = s
    /\ slen = Len(input)
    /\ failure = [i \in 0..(2 * MaxLen) |-> Sentinel]
    /\ patIdx = Sentinel /\ loopIdx = 1
    /\ bestOffset = 0
    /\ pc = "outer"

\* Outer loop: walk each rotation up to the doubled length (wrap-around scan).
Outer ==
    /\ pc = "outer"
    /\ loopIdx < MaxLoop
    /\ pc' = "lookup"
    /\ UNCHANGED <<input, slen, failure, patIdx, loopIdx, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ failure' = [failure EXCEPT ![loopIdx] = failure[bestOffset + loopIdx]]
    /\ pc' = "inner"
    /\ UNCHANGED <<input, slen, patIdx, loopIdx, bestOffset>>

Shift(i, k) == (i + k) % slen

\* Compare the current character against the candidate rotation's character.
Inner ==
    /\ pc = "inner"
    /\ input[Shift(loopIdx, bestOffset)] # input[Shift(loopIdx, patIdx)]
    /\ patIdx # Sentinel
    /\ pc' = "inner"
    /\ UNCHANGED <<input, slen, failure, patIdx, loopIdx, bestOffset>>

UpdateBest ==
    /\ pc = "inner"
    /\ input[Shift(loopIdx, bestOffset)] < input[Shift(loopIdx, patIdx)]
    /\ bestOffset' = Shift(loopIdx, bestOffset)
    /\ UNCHANGED <<input, slen, failure, patIdx, loopIdx, pc>>

FollowFailure ==
    /\ pc = "inner"
    /\ patIdx' = failure[patIdx]
    /\ pc' = "inner"
    /\ UNCHANGED <<input, slen, failure, loopIdx, bestOffset>>

Post ==
    /\ pc = "inner"
    /\ (input[Shift(loopIdx, bestOffset)] # input[Shift(loopIdx, patIdx)]
          \/ patIdx = Sentinel)
    /\ (input[Shift(loopIdx, bestOffset)] < input[Shift(loopIdx, patIdx]]
          => bestOffset' = Shift(loopIdx, bestOffset))
    /\ failure' = [failure EXCEPT ![bestOffset + loopIdx] =
                      IF patIdx = Sentinel THEN Sentinel ELSE patIdx + 1]
    /\ pc' = "increment"
    /\ UNCHANGED <<input, slen, patIdx, loopIdx>>

Increment ==
    /\ pc = "increment"
    /\ loopIdx' = loopIdx + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<input, slen, failure, patIdx, bestOffset>>

Terminate ==
    /\ pc = "outer"
    /\ loopIdx = MaxLoop
    /\ pc' = "final"
    /\ UNCHANGED <<input, slen, failure, patIdx, loopIdx, bestOffset>>

Stutter ==
    /\ pc = "final"
    /\ UNCHANGED vars

Next ==
    \/ Outer \/ Lookup \/ Inner \/ UpdateBest \/ FollowFailure
    \/ Post \/ Increment \/ Terminate \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Outer) /\ WF_vars(Lookup)
          /\ SF_vars(Inner) /\ WF_vars(Post) /\ WF_vars(Increment)

\* Correctness: the best rotation is lexicographically minimal among all.
Correctness ==
    /\ \A i \in 1..(slen - 1) :
        \A k \in 1..(slen - 1) :
            (SeqTake(SeqDrop(input, bestOffset), k)
                @ SeqTake(SeqDrop(input, i), k))
                = (SeqTake(SeqDrop(input, bestOffset), k) @ SeqTail(SeqDrop(input, i)))
    /\ \A i \in 1..(slen - 1) :
        (SeqTake(SeqDrop(input, bestOffset), slen)
            @ SeqTake(SeqDrop(input, i), slen))
            = (SeqTake(SeqDrop(input, bestOffset), slen) @ SeqDrop(input, i))

\* Liveness: the algorithm eventually reaches its final, terminating state.
Termination == <>(pc = "final")
====