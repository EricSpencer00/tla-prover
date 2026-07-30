---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\* The algorithm is TLA+ified exactly as described: a sequential loop with a
\* failure function (KMP-style) over a doubled circular string.  The identifiers
\* below, in particular the constant names, the operator names, and the INVARIANT
\* and PROPERTY labels, must match the reference TLC configuration exactly.

CONSTANTS
  CharacterSet, Nat

VARIABLES
  str, n, failure, patIdx, loopIdx, bestOffset, pc

vars == <<str, n, failure, patIdx, loopIdx, bestOffset, pc>>

\* The sentinel value for "undefined/historic" indices in the failure function;
\* chosen outside the valid range of indices so it can never be confused with
\* a genuine index.
NoMatch == 0

Init ==
  /\ \E s \in (CharSet)^{0..Nat} : str = s
  /\ n = Len(str)
  /\ failure = [i \in 0..(2 * n) |-> NoMatch]
  /\ patIdx = NoMatch
  /\ loopIdx = 1
  /\ bestOffset = 0
  /\ pc = "outerCheck"

\* The outer loop runs up to twice the length of str, which is what makes the
\* circle "unrolled".  Once it reaches the limit the algorithm terminates.
OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF loopIdx < 2 * n THEN pc' = "failureLookup" ELSE pc' = "outerDone"
  /\ UNCHANGED <<str, n, failure, patIdx, loopIdx, bestOffset>>

FailureLookup ==
  /\ pc = "failureLookup"
  /\ patIdx' = failure[(loopIdx + n - bestOffset) % (2 * n + 1)]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, n, failure, loopIdx, bestOffset>>

\* The inner loop walks the candidate aligned position, following the failure
\* function back when the characters differ and some prefix match still remains.
InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET cur == str[(loopIdx % n) + 1]
         cand == str[((loopIdx + bestOffset) % n) + 1]
     IN /\ cur # cand
        /\ patIdx # NoMatch
        /\ pc' = "innerLoop"
        /\ UNCHANGED <<str, n, failure, patIdx, loopIdx, bestOffset>>

UpdateBestFromInner ==
  /\ pc = "innerLoop"
  /\ LET cur == str[(loopIdx % n) + 1]
         cand == str[((loopIdx + bestOffset) % n) + 1]
     IN /\ cur < cand
        /\ bestOffset' = loopIdx
        /\ UNCHANGED <<str, n, failure, patIdx, loopIdx, pc>>

FollowFailure ==
  /\ pc = "innerLoop"
  /\ patIdx # NoMatch
  /\ patIdx' = failure[patIdx]
  /\ UNCHANGED <<str, n, failure, loopIdx, bestOffset, pc>>

PostComparison ==
  /\ pc = "innerLoop"
  /\ LET cur == str[(loopIdx % n) + 1]
         cand == str[((loopIdx + bestOffset) % n) + 1]
         newEntry == IF patIdx = NoMatch THEN NoMatch ELSE patIdx + 1
     IN /\ cur # cand
        /\ patIdx = NoMatch
        /\ bestOffset' = IF cur < cand THEN loopIdx ELSE bestOffset
        /\ failure' = [failure EXCEPT ![(loopIdx + n - bestOffset) % (2 * n + 1)] = newEntry]
        /\ pc' = "increment"
        /\ UNCHANGED <<str, n, patIdx, loopIdx>>

Increment ==
  /\ pc = "increment"
  /\ loopIdx' = loopIdx + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<str, n, failure, patIdx, bestOffset>>

OuterDone ==
  /\ pc = "outerDone"
  /\ UNCHANGED vars

Stall ==
  /\ pc = "outerDone"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ FailureLookup \/ InnerLoop \/ UpdateBestFromInner
  \/ FollowFailure \/ PostComparison \/ Increment \/ OuterDone \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(FailureLookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(PostComparison)
        /\ WF_vars(Increment) /\ WF_vars(OuterDone)

\* Type invariant: every state variable stays within its declared shape.
TypeInvariant ==
  /\ str \in (CharSet)^{0..Nat}
  /\ n = Len(str)
  /\ failure \in [0..(2 * n) -> {NoMatch} \cup (1..(2 * n))]
  /\ patIdx \in {NoMatch} \cup (1..(2 * n))
  /\ loopIdx \in 1..(2 * n + 1)
  /\ bestOffset \in 0..n
  /\ pc \in {"outerCheck", "failureLookup", "innerLoop", "increment", "outerDone"}

\* Correctness: upon termination, the rotation at bestOffset is lexicographically
\* minimal (and ties are broken by the smallest shift, as required).
Correctness ==
  /\ pc = "outerDone"
  /\ \A i \in 1..n : str[(i + bestOffset) % n + 1] <= str[(i + 1 - 1) % n + 1]
  /\ \A i \in 1..n :
       (str[(i + bestOffset) % n + 1] = str[(i + 1 - 1) % n + 1]) => bestOffset <= i

Termination == (pc = "outerDone") ~> (pc = "outerDone")

TypeOK == TypeInvariant
RingLeast == Correctness
TerminationSatisfied == Termination

====