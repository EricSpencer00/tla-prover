---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* The .cfg replaces the standard Nat with a finite version of it, but we keep
\* EXTENDS Naturals and never declare Nat ourselves.
[ZSequences]CharacterSet

VARIABLES inputString, length, failure, matchIdx, loop, bestOffset, pc

vars == <<inputString, length, failure, matchIdx, loop, bestOffset, pc>>

Sentinel == 0
MaxLen == 2
MaxChar == 2

\* The corpus: every zero-indexed sequence over the character set up to the
\* configured maximum length.
Corpus == {s \in Seq(CharacterSet) : Len(s) <= MaxLen}

Init ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure = [i \in 0..(2 * length) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ loop = 1
  /\ bestOffset = 0
  /\ pc = "outer"

\* Outer loop: run up to twice the string length to cover the doubled string.
Outer ==
  /\ pc = "outer"
  /\ IF loop < 2 * length
       THEN pc' = "lookup"
       ELSE pc' = "done"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, loop, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ matchIdx' = failure[loop - bestOffset]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, length, failure, loop, bestOffset>>

\* Compare the character at the current loop position with the candidate.
Compare ==
  /\ pc = "compare"
  /\ LET cur == inputString[(loop % length) + 1]
         cand == inputString[((loop - bestOffset) % length) + 1]
     IN IF cur # cand /\ matchIdx # Sentinel
          THEN pc' = "compare"
          ELSE pc' = "post"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, loop, bestOffset>>

UpdateBest ==
  /\ pc = "compare"
  /\ LET cur == inputString[(loop % length) + 1]
         cand == inputString[((loop - bestOffset) % length) + 1]
     IN cur < cand /\ bestOffset' = loop
  /\ UNCHANGED <<inputString, length, failure, matchIdx, loop, pc>>

Follow ==
  /\ pc = "compare"
  /\ matchIdx # Sentinel
  /\ matchIdx' = failure[matchIdx]
  /\ UNCHANGED <<inputString, length, failure, loop, bestOffset, pc>>

Post ==
  /\ pc = "post"
  /\ LET cur == inputString[(loop % length) + 1]
         cand == inputString[((loop - bestOffset) % length) + 1]
     IN /\ IF cur # cand /\ matchIdx = Sentinel /\ cur < cand
           THEN bestOffset' = loop
           ELSE bestOffset' = bestOffset
        /\ failure' = [failure EXCEPT ![loop - bestOffset] =
                         IF cur # cand /\ matchIdx = Sentinel
                           THEN Sentinel
                           ELSE matchIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, length, matchIdx, loop>>

Increment ==
  /\ pc = "increment"
  /\ loop' = loop + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, length, failure, matchIdx, bestOffset>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Compare \/ UpdateBest \/ Follow \/ Post \/ Increment \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(Compare) /\ WF_vars(Post) /\ WF_vars(Increment)

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure \in [0..(2 * length) -> 0..(2 * length)]
  /\ matchIdx \in 0..(2 * length)
  /\ loop \in 1..(2 * length)
  /\ bestOffset \in 0..(length - 1)

\* The rotation at bestOffset is lexicographically minimal.
Correctness ==
  /\ pc = "done"
  /\ \A i \in 0..(length - 1) :
       LET rot(o) == <<inputString[((o + k) % length) + 1] : k \in 0..(length - 1)>>
       IN rot(bestOffset) <= rot(i)
  /\ \A i \in 0..(length - 1) :
       rot(bestOffset) = rot(i) => bestOffset <= i

Termination == <>(pc = "done")

====