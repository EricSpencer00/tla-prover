---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS
  CharacterSet, Nat

\* IndexOf is the linear search version; there is no built-in sequence search, so
\* the auxiliary definition below is used only inside Correctness, where it is
\* bounded by the string length and thus harmless for model checking.
IndexOf(s, sub) == CHOOSE k \in 0..(Len(s) - Len(sub)) : \A i \in 1..Len(sub) : s[k + i] = sub[i]

VARIABLES
  inputString, length, failure, patternIdx, loopIdx, bestOffset, pc

vars == <<inputString, length, failure, patternIdx, loopIdx, bestOffset, pc>>

Token == Nat
Sentinel == 99

Corpus == [n \in Nat |-> CHOOSE s \in [1..n -> CharacterSet] : TRUE]

TypeInvariant ==
  /\ inputString \in Corpus
  /\ length = Len(inputString)
  /\ failure \in [0..(2 * length) -> 0..(2 * length) \cup {Sentinel}]
  /\ patternIdx \in 0..(2 * length) \cup {Sentinel}
  /\ loopIdx \in 0..(2 * length)
  /\ bestOffset \in 0..(length - 1)
  /\ pc \in {"outer", "lookup", "inner", "compare", "fail", "post", "done"}

Init ==
  /\ \E s \in Corpus :
       /\ inputString = s
       /\ length = Len(s)
  /\ failure = [k \in 0..(2 * Nat) |-> Sentinel]
  /\ patternIdx = Sentinel
  /\ loopIdx = 1
  /\ bestOffset = 0
  /\ pc = "outer"

\* (1) Outer loop check: continue while under the bound, otherwise terminate.
Outer ==
  /\ pc = "outer"
  /\ IF loopIdx < 2 * length
       THEN pc' = "lookup"
       ELSE pc' = "done"
  /\ UNCHANGED <<inputString, length, failure, patternIdx, loopIdx, bestOffset>>

\* (2) Failure function lookup at the current position relative to best offset.
Lookup ==
  /\ pc = "lookup"
  /\ patternIdx' = failure[(loopIdx + bestOffset) % length]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, length, failure, loopIdx, bestOffset>>

\* (3) Inner comparison loop: bail early if both chars differ and patternIdx is
\* still defined; otherwise exit to the post-comparison step.
Inner ==
  /\ pc = "inner"
  /\ LET cur == inputString[(loopIdx % length) + 1]
         cand == inputString[((loopIdx + patternIdx) % length) + 1] IN
     IF cur # cand /\ patternIdx # Sentinel
       THEN pc' = "compare"
       ELSE pc' = "post"
  /\ UNCHANGED <<inputString, length, failure, patternIdx, loopIdx, bestOffset>>

\* (4) If the current char is less, the candidate rotation is not minimal: update.
Compare ==
  /\ pc = "compare"
  /\ LET cur == inputString[(loopIdx % length) + 1]
         cand == inputString[((loopIdx + patternIdx) % length) + 1] IN
     /\ cur < cand => bestOffset' = loopIdx % length
  /\ UNCHANGED <<inputString, length, failure, patternIdx, loopIdx, pc>>

\* (5) Follow the failure function chain.
Fail ==
  /\ pc = "compare"
  /\ patternIdx' = failure[patternIdx]
  /\ pc' = "inner"
  /\ UNCHANGED <<inputString, length, failure, loopIdx, bestOffset>>

\* (6) Post-comparison: if chars differ and patternIdx is Sentinel, re-check and
\* update the best offset; otherwise, advance or reset the failure function.
Post ==
  /\ pc = "post"
  /\ LET cur == inputString[(loopIdx % length) + 1]
         cand == inputString[((loopIdx + patternIdx) % length) + 1] IN
     /\ IF cur # cand /\ patternIdx = Sentinel /\ cur < cand
          THEN bestOffset' = loopIdx % length
          ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![loopIdx] = IF cur # cand /\ patternIdx = Sentinel
                                            THEN Sentinel ELSE patternIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<inputString, length, patternIdx, loopIdx>>

\* (7) Increment loop counter and return to the outer check.
Increment ==
  /\ pc = "increment"
  /\ loopIdx' = loopIdx + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, length, failure, patternIdx, bestOffset>>

\* Stuttering: once terminated, the algorithm may simply stay in place.
Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Outer \/ Lookup \/ Inner \/ Compare \/ Fail \/ Post \/ Increment \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Outer)

\* Correctness: the rotation at bestOffset is lexicographically smallest, and
\* among equal rotations it has the smallest shift value.
Correctness ==
  /\ pc = "done"
  /\ \A i \in 1..length :
       inputString[(bestOffset + i - 1) % length + 1] <= inputString[i]
  /\ \A i \in 1..length :
       inputString[(bestOffset + i - 1) % length + 1] = inputString[i]
         => bestOffset <= i - 1

Termination == <>(pc = "done")

\* The reference configuration also projects the label-level actions for coverage.
NextLabel == {Outer, Lookup, Inner, Compare, Fail, Post, Increment, Stall}

====