---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

CONSTANTS CharacterSet

ZSequences == [x \in 0..9 |-> x]

RECURSIVE Rotated(_)
Rotated(a) ==
  IF a = <<>> THEN <<>>
  ELSE LET n == Len(a) IN [i \in 0..(n-1) |-> a[(i % n) + 1]]

VARIABLES input, n, fail, pIdx, i, best, pc

vars == <<input, n, fail, pIdx, i, best, pc>>

Sentinel == n

TypeInvariant ==
  /\ input \in ZSequences
  /\ n = Len(input)
  /\ fail \in [0..(2*n) -> (0..n) \cup {Sentinel}]
  /\ pIdx \in 0..n \cup {Sentinel}
  /\ i \in 1..(2*n)
  /\ best \in 0..(n-1)
  /\ pc \in {"outerCheck", "compare", "postCompare", "done"}

Init ==
  /\ input \in ZSequences
  /\ n = Len(input)
  /\ fail = [k \in 0..(2*n) |-> Sentinel]
  /\ pIdx = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF i < (2*n) THEN pc' = "compare" ELSE pc' = "done"
  /\ UNCHANGED <<input, n, fail, pIdx, i, best>>

Lookup ==
  /\ pc = "compare"
  /\ pIdx' = fail[best + i]
  /\ pc' = "compare"
  /\ UNCHANGED <<input, n, fail, i, best>>

Differ(a, b) == input[(a % n) + 1] # input[(b % n) + 1]

InnerLoop ==
  /\ pc = "compare"
  /\ Differ(best + i, best + pIdx)
  /\ pIdx # Sentinel
  /\ pc' = "compare"
  /\ UNCHANGED <<input, n, fail, pIdx, i, best>>

UpdateBestOnLess ==
  /\ pc = "compare"
  /\ Differ(best + i, best + pIdx)
  /\ pIdx # Sentinel
  /\ input[((best + i) % n) + 1] < input[((best + pIdx) % n) + 1]
  /\ best' = (best + i) % n
  /\ UNCHANGED <<input, n, fail, pIdx, i, pc>>

FollowChain ==
  /\ pc = "compare"
  /\ pIdx # Sentinel
  /\ pIdx' = fail[pIdx]
  /\ UNCHANGED <<input, n, fail, i, best, pc>>

PostComparison ==
  /\ pc = "compare"
  /\ pIdx = Sentinel \/ ~Differ(best + i, best + pIdx)
  /\ IF Differ(best + i, best + pIdx) THEN
       IF input[((best + i) % n) + 1] < input[((best + pIdx) % n) + 1]
         THEN best' = (best + i) % n
         ELSE best' = best
     ELSE best' = best
  /\ fail' = [fail EXCEPT ![best + i] = IF pIdx = Sentinel THEN Sentinel ELSE pIdx + 1]
  /\ pc' = "postCompare"
  /\ UNCHANGED <<input, n, pIdx, i>>

Increment ==
  /\ pc \in {"postCompare", "compare"}
  /\ i' = i + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<input, n, fail, pIdx, best>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ InnerLoop \/ UpdateBestOnLess
  \/ FollowChain \/ PostComparison \/ Increment \/ Done \/ Stall

Spec == Init /\ [][Next]_vars

Correctness ==
  /\ pc = "done"
  /\ \A j \in 0..(n-1) : Rotated(input)[best] <= Rotated(input)[j]
  /\ \A j \in 0..(n-1) : Rotated(input)[best] = Rotated(input)[j] => best <= j

Terminating == <>(pc = "done")

====