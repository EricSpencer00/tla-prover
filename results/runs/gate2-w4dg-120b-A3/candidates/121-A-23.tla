---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

\* The alphabet is a finite subset of Nat, adjusted at model-check time.
CONSTANTS CharacterSet

VARIABLES inputString, stringLen, failure, matchIdx, outer, bestOffset, pc

vars == <<inputString, stringLen, failure, matchIdx, outer, bestOffset, pc>>

MaxLen == 2
Sentinel == MaxLen
MaxChar == 2

\* The corpus: every zero-indexed sequence over CharacterSet up to MaxLen.
Corpus == { s \in [0..MaxLen -> CharacterSet] : Len(s) <= MaxLen }

\* Wrap an index into the current string length to get a circular position.
Circ(i) == i % stringLen

\* Lexicographic compare of two rotations of the input string.
LessRot(a, b) ==
  \/ LET k == 0
     IN \E k \in 0..(MaxLen - 1) : \A i \in 0..(MaxLen - 1) :
          IF inputString[Circ(a + i)] = inputString[Circ(b + i)] THEN TRUE ELSE i >= k
  \/ inputString[Circ(a + k)] < inputString[Circ(b + k)]

TypeInvariant ==
  /\ inputString \in Corpus
  /\ stringLen = Len(inputString)
  /\ stringLen >= 1
  /\ failure \in [0..(2 * MaxLen - 1) -> 0..Sentinel]
  /\ matchIdx \in 0..Sentinel
  /\ outer \in 1..(2 * MaxLen)
  /\ bestOffset \in 0..(MaxLen - 1)
  /\ pc \in {"outer", "lookup", "compare", "done"}

\* Outer-loop entry: the algorithm runs up to twice the string length.
Init ==
  /\ inputString \in Corpus
  /\ stringLen = Len(inputString)
  /\ failure = [i \in 0..(2 * MaxLen - 1) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ outer = 1
  /\ bestOffset = 0
  /\ pc = "outer"

Outer ==
  /\ pc = "outer"
  /\ outer < 2 * MaxLen
  /\ pc' = "lookup"
  /\ UNCHANGED <<inputString, stringLen, failure, matchIdx, outer, bestOffset>>

Lookup ==
  /\ pc = "lookup"
  /\ failure' = [failure EXCEPT ![Circ(outer)] = failure[Circ(outer - 1)]]
  /\ matchIdx' = failure[Circ(outer - 1)]
  /\ pc' = "compare"
  /\ UNCHANGED <<inputString, stringLen, outer, bestOffset>>

\* Inner comparison loop: compare the character at the current outer position
\* with the character at the candidate position given by the failure link.
Compare ==
  /\ pc = "compare"
  /\ LET cur == inputString[Circ(outer)]
     cand == inputString[Circ(bestOffset + matchIdx + 1)]
  IN
    /\ (cur # cand /\ matchIdx # Sentinel)
       \/ (cur # cand /\ matchIdx = Sentinel)
       \/ (cur = cand)
    /\ IF cur < cand /\ cur # cand
         THEN bestOffset' = Circ(matchIdx + 1)
         ELSE bestOffset' = bestOffset
    /\ IF cur # cand
         THEN failure' = [failure EXCEPT ![Circ(outer)] = IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1]
         ELSE failure' = [failure EXCEPT ![Circ(outer)] = Sentinel]
    /\ matchIdx' = IF matchIdx = Sentinel THEN Sentinel ELSE failure[matchIdx]
    /\ pc' = "done"
    /\ UNCHANGED <<inputString, stringLen, outer>>

Done ==
  /\ pc = "done"
  /\ outer' = outer + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<inputString, stringLen, failure, matchIdx, bestOffset>>

Stall ==
  /\ outer >= 2 * MaxLen
  /\ pc = "outer"
  /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Compare \/ Done \/ Stall

Spec == Init /\ [][Next]_vars

\* Correctness: the found rotation is lexicographically <= every other.
Correctness ==
  \A off \in 0..(stringLen - 1) : LessRot(bestOffset, off)

Termination == <>(pc = "outer" /\ outer >= 2 * MaxLen)

====