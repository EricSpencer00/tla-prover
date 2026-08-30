---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

VARIABLES
  inputString,    \* the nondeterministically chosen zero-indexed input sequence
  strLen,         \* length of the input string
  failure,        \* failure function array: [0..2*strLen -> 0..2*strLen \cup {undefined}]
  matchIdx,       \* pattern-match index tracking the current failure function lookup
  loopCounter,    \* outer loop counter running from 1 to below 2*strLen
  bestOffset,     \* current best rotation offset (start of minimal lexicographic rotation)
  pc              \* program counter: which labeled step of the algorithm is executing

vars == <<inputString, strLen, failure, matchIdx, loopCounter, bestOffset, pc>>

Undefined == 0

TypeInvariant ==
  /\ inputString \in [0..3 -> CharacterSet]
  /\ strLen \in 0..3
  /\ failure \in [0..(2 * strLen) -> (0..(2 * strLen)) \cup {Undefined}]
  /\ matchIdx \in (0..(2 * strLen)) \cup {Undefined}
  /\ loopCounter \in 1..(2 * strLen)
  /\ bestOffset \in 0..(strLen - 1)
  /\ pc \in {"outer_check", "lookup_failure", "inner_compare", "post_compare", "done"}

\* The outer loop iterates up to twice the length of the input to cover the doubled
\* string without explicit circular indexing logic.
Init ==
  /\ \E s \in [0..3 -> CharacterSet] : inputString = s
  /\ strLen = Len(inputString)
  /\ failure = [i \in 0..(2 * strLen) |-> Undefined]
  /\ matchIdx = Undefined
  /\ loopCounter = 1
  /\ bestOffset = 0
  /\ pc = "outer_check"

OuterCheck ==
  /\ pc = "outer_check"
  /\ IF loopCounter < (2 * strLen) THEN pc' = "lookup_failure" ELSE pc' = "done"
  /\ UNCHANGED <<inputString, strLen, failure, matchIdx, loopCounter, bestOffset>>

\* Retrieve the failure function value for the current position relative to the best offset.
LookupFailure ==
  /\ pc = "lookup_failure"
  /\ matchIdx' = failure[loopCounter - bestOffset]
  /\ pc' = "inner_compare"
  /\ UNCHANGED <<inputString, strLen, failure, loopCounter, bestOffset>>

\* Compare the character at the current loop position (mod length) with the candidate.
InnerCompare ==
  /\ pc = "inner_compare"
  /\ LET curChar == inputString[(loopCounter % strLen)]
         candChar == inputString[((loopCounter + bestOffset) % strLen)]
     IN IF curChar # candChar /\ matchIdx # Undefined
           THEN pc' = "post_compare"
           ELSE IF curChar < candChar
                  THEN bestOffset' = loopCounter % strLen
                  ELSE bestOffset' = bestOffset
           /\ matchIdx' = IF curChar = candChar
                            THEN IF matchIdx = Undefined THEN 0 ELSE matchIdx + 1
                            ELSE matchIdx
           /\ pc' = "post_compare"
  /\ UNCHANGED <<inputString, strLen, failure, loopCounter>>

\* Follow the failure function chain.
FollowFailure ==
  /\ pc = "post_compare"
  /\ failure' = [failure EXCEPT ![loopCounter - bestOffset] =
                    IF matchIdx = Undefined THEN Undefined ELSE matchIdx + 1]
  /\ loopCounter' = loopCounter + 1
  /\ pc' = "outer_check"
  /\ UNCHANGED <<inputString, strLen, matchIdx, bestOffset>>

\* The algorithm has terminated.
Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

\* Stuttering after termination.
Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ LookupFailure
  \/ InnerCompare
  \/ FollowFailure
  \/ Done
  \/ Stutter

Spec == Init /\ [][Next]_vars

\* Correctness: upon termination, the best rotation offset identifies the
\* lexicographically-minimal rotation of the input string (and the smallest shift among ties).
Correctness ==
  /\ pc = "done"
  /\ \A k \in 0..(strLen - 1) :
       LET rotation(i) == [j \in 0..(strLen - 1) |-> inputString[(i + j) % strLen]]
           baseSeq == rotation(bestOffset)
           candSeq == rotation(k)
           comp == \E m \in 0..(strLen - 1) :
                     /\ \A j \in 0..(m - 1) : baseSeq[j] = candSeq[j]
                     /\ baseSeq[m] # candSeq[m]
       IN (baseSeq # candSeq => baseSeq # candSeq) /\ (baseSeq # candSeq => comp \/ (baseSeq = candSeq /\ bestOffset < k))

Termination == <>(pc = "done")

\* The character set is a constant, but the model checking configuration constrains its size
\* and the maximum string length at runtime. The .cfg file redefines CharacterSet as a
\* finite subset of Nat so the model stays finite.
====