---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Zero-indexed sequences over a finite character set, with a sentinel value
\* for "undefined" that is one past the highest valid index.
\* The algorithm runs in linear time and finds the lexicographically-least
\* rotation of a circular string, following Booth's 1980 algorithm.
\* The model checker explores all strings up to the configured length.

Sentinel == 99

VARIABLES inputString, strLen, failure, patIdx, loop, bestOffset, pc

vars == <<inputString, strLen, failure, patIdx, loop, bestOffset, pc>>

Corpus == UNION { [1 .. n -> CharacterSet] : n \in Nat }

TypeInvariant ==
  /\ inputString \in Corpus
  /\ strLen = Len(inputString)
  /\ failure \in [0 .. 2 * strLen -> 0 .. 2 * strLen \cup {Sentinel}]
  /\ patIdx \in 0 .. 2 * strLen \cup {Sentinel}
  /\ loop \in 1 .. 2 * strLen
  /\ bestOffset \in 0 .. (strLen - 1)
  /\ pc \in {"outer", "lookup", "inner", "post", "done"}

Init ==
  /\ \E s \in Corpus : inputString = s
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
  /\ failure' = [failure EXCEPT ![loop - bestOffset] = failure[loop - bestOffset]]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, strLen, patIdx, loop, bestOffset>>

\* Compare the character at the current loop position with the character at
\* the candidate position (both modulo the string length). If they differ and
\* the pattern-match index is not the sentinel, continue the inner loop.
InnerLoop ==
  /\ pc = "inner"
  /\ LET curChar == inputString[(loop % strLen) + 1]
         candChar == inputString[((loop - bestOffset) % strLen) + 1] IN
       IF curChar # candChar /\ patIdx # Sentinel
         THEN pc' = "inner"
         ELSE pc' = "post"
  /\ UNCHANGED <<inputString, strLen, failure, patIdx, loop, bestOffset>>

UpdateOnLess ==
  /\ pc = "inner"
  /\ LET curChar == inputString[(loop % strLen) + 1]
         candChar == inputString[((loop - bestOffset) % strLen) + 1] IN
       IF curChar < candChar
         THEN bestOffset' = loop
         ELSE bestOffset' = bestOffset
  /\ UNCHANGED <<inputString, strLen, failure, patIdx, loop, pc>>

FollowFailure ==
  /\ pc = "inner"
  /\ patIdx' = failure[loop - bestOffset]
  /\ UNCHANGED <<inputString, strLen, failure, loop, bestOffset, pc>>

PostComparison ==
  /\ pc = "post"
  /\ LET curChar == inputString[(loop % strLen) + 1]
         candChar == inputString[((loop - bestOffset) % strLen) + 1] IN
       IF curChar # candChar /\ patIdx = Sentinel
         THEN bestOffset' = IF curChar < candChar THEN loop ELSE bestOffset
         ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![loop - bestOffset] =
                   IF curChar # candChar THEN Sentinel ELSE patIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, strLen, patIdx, loop>>

Increment ==
  /\ pc = "increment"
  /\ loop' = loop + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, strLen, failure, patIdx, bestOffset>>

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
  \/ Increment
  \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(Lookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(UpdateOnLess) /\ WF_vars(FollowFailure)
        /\ WF_vars(PostComparison) /\ WF_vars(Increment)

\* The best rotation offset identifies the lexicographically-minimal rotation
\* of the input string: it is less than or equal to every other rotation, and
\* among equal rotations it has the smallest shift value.
Correctness ==
  /\ \A i \in 0 .. (strLen - 1) :
       LET rotA == [k \in 1 .. strLen |-> inputString[((bestOffset + k) % strLen) + 1]]
           rotB == [k \in 1 .. strLen |-> inputString[((i + k) % strLen) + 1]] IN
         (rotA # rotB) => (rotA \prec rotB)
  /\ \A i \in 0 .. (strLen - 1) :
       LET rotA == [k \in 1 .. strLen |-> inputString[((bestOffset + k) % strLen) + 1]]
           rotB == [k \in 1 .. strLen |-> inputString[((i + k) % strLen) + 1]] IN
         (rotA = rotB) => (bestOffset <= i)

Termination == <>(pc = "done")

====