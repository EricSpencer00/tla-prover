---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Redefine the natural-number operator the .cfg expects to be overridden:
\* Nat is kept from Naturals for arithmetic, but CharacterSet is finite.
CharacterSet == Nat

\* The corpus is the set of all zero-indexed strings over the character set.
Corpus == UNION { [1..n -> CharacterSet] : n \in Nat }

\* The sentinel value meaning "failure function undefined".
NoMatch == 0
After(i) == i + 1

VARIABLES string, length, failure, match, loop, best, pc

vars == <<string, length, failure, match, loop, best, pc>>

TypeInvariant ==
    /\ string \in Corpus
    /\ length = Len(string)
    /\ failure \in [0 .. (2 * length) -> 0 .. (length + 1)]
    /\ match \in 0 .. (length + 1)
    /\ loop \in 1 .. (2 * length)
    /\ best \in 0 .. (length - 1)
    /\ pc \in {"outer", "lookup", "inner", "update", "follow", "post", "done"}

Init ==
    /\ string \in Corpus
    /\ length = Len(string)
    /\ failure = [i \in 0 .. (2 * length) |-> NoMatch]
    /\ match = NoMatch
    /\ loop = 1
    /\ best = 0
    /\ pc = "outer"

OuterLoop ==
    /\ pc = "outer"
    /\ loop < (2 * length)
    /\ pc' = "lookup"
    /\ UNCHANGED <<string, length, failure, match, loop, best>>

LookupFailure ==
    /\ pc = "lookup"
    /\ failure[(loop - best) % length] # NoMatch
    /\ match' = failure[(loop - best) % length]
    /\ pc' = "inner"
    /\ UNCHANGED <<string, length, failure, loop, best>>

\* Compare characters at the current offset and the candidate offset.
InnerLoop ==
    /\ pc = "inner"
    /\ string[(loop % length)] # string[((loop + match) % length)]
    /\ \/ match = NoMatch
       \/ failure[(match - best) % length] # NoMatch
    /\ pc' = "post"
    /\ UNCHANGED <<string, length, failure, match, loop, best>>

UpdateBest ==
    /\ pc = "inner"
    /\ match # NoMatch
    /\ string[(loop % length)] < string[((loop + match) % length)]
    /\ best' = loop
    /\ pc' = "follow"
    /\ UNCHANGED <<string, length, failure, match, loop>>

FollowFailure ==
    /\ pc = "follow"
    /\ match # NoMatch
    /\ failure[(match - best) % length] # NoMatch
    /\ match' = failure[(match - best) % length]
    /\ pc' = "inner"
    /\ UNCHANGED <<string, length, failure, loop, best>>

SetFailure ==
    /\ pc \in {"lookup", "follow"}
    /\ match # NoMatch
    /\ failure' = [failure EXCEPT ![(loop - best) % length] = After(match)]
    /\ pc' = "post"
    /\ UNCHANGED <<string, length, match, loop, best>>

ResetFailure ==
    /\ pc \in {"lookup", "follow"}
    /\ match = NoMatch
    /\ failure' = [failure EXCEPT ![(loop - best) % length] = NoMatch]
    /\ pc' = "post"
    /\ UNCHANGED <<string, length, match, loop, best>>

PostComparison ==
    /\ pc = "post"
    /\ \/ string[(loop % length)] # string[((loop + match) % length)]
       /\ match = NoMatch
       /\ \/ match' = NoMatch
          \/ (string[(loop % length)] < string[((loop + match) % length)]
              /\ best' = loop)
    /\ pc' = "incr"
    /\ UNCHANGED <<string, length, failure, loop>>

IncrLoop ==
    /\ pc = "incr"
    /\ loop' = loop + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<string, length, failure, match, best>>

Done ==
    /\ pc = "outer"
    /\ loop = (2 * length)
    /\ pc' = "done"
    /\ UNCHANGED <<string, length, failure, match, loop, best>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterLoop \/ LookupFailure \/ InnerLoop \/ UpdateBest \/ FollowFailure
    \/ SetFailure \/ ResetFailure \/ PostComparison \/ IncrLoop \/ Done \/ Stall

\* The algorithm always reaches its final state (regardless of string).
Termination == <>(pc = "done")

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(IncrLoop)

\* The rotation labeled by the best offset is lexicographically minimal,
\* and among equivalent rotations it is the one with the smallest shift.
Correctness ==
    /\ \A m \in 0 .. (length - 1) : \A i \in 0 .. (length - 1) :
         string[(best + i) % length] <= string[(m + i) % length]
    /\ \A m \in 0 .. (length - 1) :
         (string[(best + 1) % length] = string[(m + 1) % length]
            /\ string[(best + 2) % length] = string[(m + 2) % length])
            => best <= m

====