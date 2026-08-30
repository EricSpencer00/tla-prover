---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* The linear-time algorithm Booth proved in 1980: given a string viewed
\* circularly, find the rotation that yields the lexicographically
\* smallest string.  The failure function is exactly the one KMP uses.
\* The model chooses the input string nondeterministically from all
\* zero-indexed sequences over the character set, so correctness covers
\* every possible input up to the configured maximum length.

CONSTANTS CharacterSet

Uninitialized == 99
Corpus == Union({[1 .. n -> 0 .. Uninitialized] : n \in 1 .. 2})
StringsOf(S) == {s \in Corpus : Len(s) <= S}
Offsets == 0 .. 2

VARIABLES chars, size, nextSmaller, patternMatch, loopCount, bestOffset, pc

vars == <<chars, size, nextSmaller, patternMatch, loopCount, bestOffset, pc>>

\* A lexicographically smaller rotation strictly dominates an equal one:
\* the smallest shift that achieves the minimum is the answer Booth
\* proved is unique (modulo the string length).
AtMinimallyShifted(s, o) == \A i \in 1 .. Len(s) :
  s[(o + i) % Len(s)] < s[i] \/ (s[(o + i) % Len(s)] = s[i] /\ o <= i - 1)

TypeInvariant ==
  /\ chars \in StringsOf(2)
  /\ size = Len(chars)
  /\ nextSmaller \in [0 .. 2 * size -> (0 .. size) \cup {Uninitialized}]
  /\ patternMatch \in (0 .. size) \cup {Uninitialized}
  /\ loopCount \in Offsets
  /\ bestOffset \in 0 .. (size > 0 /\ size - 1)
  /\ pc \in {"outer", "post", "done"}

Init ==
  /\ \E s \in StringsOf(2) :
       /\ chars = s
       /\ size = Len(s)
       /\ nextSmaller = [i \in 0 .. 2 * Len(s) |-> Uninitialized]
  /\ patternMatch = Uninitialized
  /\ loopCount = 1
  /\ bestOffset = 0
  /\ pc = "outer"

\* The outer loop walks the doubled string and carries the KMP match
\* length forward across it; the inner loop does the character-wise
\* comparison for the failure function entry currently being built.
OuterCheck ==
  /\ pc = "outer"
  /\ IF loopCount < 2 * size
     THEN /\ pc' = "post"
          /\ patternMatch' = nextSmaller[loopCount - 1]
          /\ UNCHANGED <<chars, size, nextSmaller, loopCount, bestOffset>>
     ELSE /\ pc' = "done"
          /\ UNCHANGED <<chars, size, nextSmaller, patternMatch, loopCount, bestOffset>>

PostComparison ==
  /\ pc = "post"
  /\ chars[(loopCount - 1) % size] # chars[(bestOffset + loopCount - 1) % size]
  /\ IF patternMatch = Uninitialized
       THEN IF chars[(loopCount - 1) % size] < chars[(bestOffset + loopCount - 1) % size]
             THEN bestOffset' = loopCount - 1
             ELSE bestOffset' = bestOffset
            /\ nextSmaller' = [nextSmaller EXCEPT ![loopCount] = Uninitialized]
       ELSE bestOffset' = IF chars[(loopCount - 1) % size] < chars[(bestOffset + loopCount - 1) % size]
                           THEN loopCount - 1 ELSE bestOffset
            /\ nextSmaller' = [nextSmaller EXCEPT ![loopCount] = patternMatch + 1]
  /\ loopCount' = loopCount + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<chars, size, patternMatch>>

FollowFailure ==
  /\ pc = "post"
  /\ chars[(loopCount - 1) % size] = chars[(bestOffset + loopCount - 1) % size]
  /\ patternMatch # Uninitialized
  /\ patternMatch' = nextSmaller[loopCount - 1]
  /\ UNCHANGED <<chars, size, nextSmaller, loopCount, bestOffset, pc>>

ContinueLoop ==
  \/ OuterCheck \/ PostComparison \/ FollowFailure
  /\ pc # "done"

Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == ContinueLoop \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(ContinueLoop)

Correctness == AtMinimallyShifted(chars, bestOffset)

Termination == pc = "done"

====