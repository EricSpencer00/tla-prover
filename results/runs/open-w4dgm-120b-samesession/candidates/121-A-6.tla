---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* Zero-indexed sequence: the k-th character of s (mod the length of s)
Index(s, k) == s[(k % Len(s)) + 1]

NotFound == 0 - 1

VARIABLES s, n, failure, patIdx, outer, bestOffset, pc

vars == <<s, n, failure, patIdx, outer, bestOffset, pc>>

TypeInvariant ==
  /\ s \in [1..CharacterSet]^*
  /\ n = Len(s)
  /\ failure \in [0..(2 * n) -> (0..(2 * n)) \union {NotFound}]
  /\ patIdx \in (0..(2 * n)) \union {NotFound}
  /\ outer \in 0..(2 * n)
  /\ bestOffset \in 0..(n - 1)
  /\ pc \in {"outerLoop", "failureLookup", "innerLoop", "postCompare", "terminated"}

\* The lexicographically-minimal rotation of s starts at bestOffset.
Correctness ==
  /\ \A shift \in 0..(n - 1) : \A pos \in 0..(n - 1) :
       Index(s, bestOffset + pos) <= Index(s, shift + pos)
  /\ \A shift \in 0..(n - 1) :
       ((\A pos \in 0..(n - 1) : Index(s, bestOffset + pos) = Index(s, shift + pos))
        => bestOffset <= shift)

Init ==
  /\ \E w \in [1..CharacterSet]^* : s = w
  /\ n = Len(s)
  /\ failure = [i \in 0..(2 * n) |-> NotFound]
  /\ patIdx = NotFound
  /\ outer = 1
  /\ bestOffset = 0
  /\ pc = "outerLoop"

OuterLoop ==
  /\ pc = "outerLoop"
  /\ IF outer < 2 * n
     THEN pc' = "failureLookup"
     ELSE pc' = "terminated"
  /\ UNCHANGED <<s, n, failure, patIdx, outer, bestOffset>>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ patIdx = failure[outer - 1]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<s, n, failure, outer, bestOffset>>

\* An inner comparison of the current character against the candidate
\* (wrapped) character; this test is the only place that can move bestOffset.
InnerLoop ==
  /\ pc = "innerLoop"
  /\ \/ Index(s, outer) # Index(s, bestOffset + patIdx)
     \/ patIdx = NotFound
  /\ IF Index(s, outer) < Index(s, bestOffset + patIdx)
     THEN bestOffset' = outer
     ELSE bestOffset' = bestOffset
  /\ pc' = "postCompare"
  /\ UNCHANGED <<s, n, failure, patIdx, outer>>

PostCompare ==
  /\ pc = "postCompare"
  /\ \/ Index(s, outer) # Index(s, bestOffset + patIdx)
     \/ patIdx = NotFound
  /\ IF Index(s, outer) < Index(s, bestOffset + patIdx)
     THEN bestOffset' = outer
     ELSE bestOffset' = bestOffset
  /\ failure' = [failure EXCEPT ![outer] =
        IF patIdx = NotFound THEN NotFound ELSE patIdx + 1]
  /\ patIdx' = failure[outer]
  /\ outer' = outer + 1
  /\ pc' = "outerLoop"
  /\ UNCHANGED s

Next == OuterLoop \/ FailureLookup \/ InnerLoop \/ PostCompare

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterLoop) /\ WF_vars(FailureLookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(PostCompare)

Termination == <>(pc = "terminated")

\* CharacterSet must stay a FINITE subset of Nat for model checking.
CharacterSet == {0, 1}
====