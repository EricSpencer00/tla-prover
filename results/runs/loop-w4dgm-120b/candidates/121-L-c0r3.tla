---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Zero-indexed sequences over a finite character set, with a sentinel value
\* for "undefined" that is one past the maximum valid index.
Zero == 0
Sentinel == 99

VARIABLES inputString, strLen, failure, patIdx, loop, bestOffset, pc

vars == <<inputString, strLen, failure, patIdx, loop, bestOffset, pc>>

Corpus == UNION { [1 .. n -> CharacterSet] : n \in Nat }

TypeInvariant ==
    /\ inputString \in Corpus
    /\ strLen = Len(inputString)
    /\ failure \in [0 .. 2 * strLen -> 0 .. strLen \cup {Sentinel}]
    /\ patIdx \in 0 .. strLen \cup {Sentinel}
    /\ loop \in 0 .. 2 * strLen
    /\ bestOffset \in 0 .. (strLen - 1)
    /\ pc \in {"outer", "lookup", "inner", "post", "done"}

Init ==
    /\ inputString \in Corpus
    /\ strLen = Len(inputString)
    /\ failure = [i \in 0 .. 2 * strLen |-> Sentinel]
    /\ patIdx = Sentinel
    /\ loop = 1
    /\ bestOffset = 0
    /\ pc = "outer"

OuterLoop ==
    /\ pc = "outer"
    /\ IF loop < 2 * strLen THEN pc' = "lookup" ELSE pc' = "done"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loop, bestOffset>>

Lookup ==
    /\ pc = "lookup"
    /\ failure' = [failure EXCEPT ![loop % strLen] = failure[bestOffset]]
    /\ pc' = "inner"
    /\ UNCHANGED <<inputString, strLen, patIdx, loop, bestOffset>>

\* The inner loop walks the failure chain, comparing characters of the
\* candidate rotation against the current best.
InnerLoop ==
    /\ pc = "inner"
    /\ IF inputString[loop % strLen] # inputString[(bestOffset + loop) % strLen]
          /\ patIdx # Sentinel
       THEN pc' = "inner"
       ELSE pc' = "post"
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loop, bestOffset>>

UpdateOnLess ==
    /\ pc = "inner"
    /\ inputString[loop % strLen] < inputString[(bestOffset + loop) % strLen]
    /\ bestOffset' = loop % strLen
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, loop, pc>>

FollowFailure ==
    /\ pc = "inner"
    /\ patIdx' = failure[patIdx]
    /\ UNCHANGED <<inputString, strLen, failure, loop, bestOffset, pc>>

PostComparison ==
    /\ pc = "post"
    /\ IF inputString[loop % strLen] # inputString[(bestOffset + loop) % strLen]
          /\ patIdx = Sentinel
          /\ inputString[loop % strLen] < inputString[(bestOffset + loop) % strLen]
       THEN bestOffset' = loop % strLen
       ELSE bestOffset' = bestOffset
    /\ failure' = [failure EXCEPT ![loop % strLen] =
                     IF inputString[loop % strLen] # inputString[(bestOffset + loop) % strLen]
                     THEN Sentinel ELSE patIdx + 1]
    /\ pc' = "outer"
    /\ UNCHANGED <<inputString, strLen, patIdx, loop>>

IncrementLoop ==
    /\ pc = "outer"
    /\ loop' = loop + 1
    /\ UNCHANGED <<inputString, strLen, failure, patIdx, bestOffset, pc>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterLoop
    \/ Lookup
    \/ InnerLoop
    \/ UpdateOnLess
    \/ FollowFailure
    \/ PostComparison
    \/ IncrementLoop
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(Lookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(UpdateOnLess) /\ WF_vars(FollowFailure)
        /\ WF_vars(PostComparison) /\ WF_vars(IncrementLoop)

\* The best rotation is lexicographically minimal and, among equal rotations,
\* has the smallest shift value.
Correctness ==
    /\ \A i \in 0 .. (strLen - 1) :
         \A j \in 0 .. (strLen - 1) :
           LET a == [k \in 0 .. (strLen - 1) |-> inputString[(i + k) % strLen]]
               b == [k \in 0 .. (strLen - 1) |-> inputString[(j + k) % strLen]]
           IN (a # b) => (a # b \/ i <= j)
    /\ pc = "done"

Termination == <>(pc = "done")

\* The character set is a finite subset of Nat, so the model stays finite.
CharacterSet == {0, 1, 2}

====