---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* The reference .cfg replaces the built-in Nat operator from Naturals
\* with an integer-valued CharacterSet. EXTENDS Naturals is still needed
\* for the natural-number machinery (modulus, comparison, etc.).
\* By assigning CharacterSet the same values as Nat we keep the spec
\* checkable while obeying the required rename.
[ZSequences]CharacterSet

CONSTANTS
  CharacterSet

Sentinel == 999

VARIABLES
  str, n, fail, matchIdx, i, best, pc

vars == <<str, n, fail, matchIdx, i, best, pc>>

TypeInvariant ==
  /\ str \in CHARACTERSET
  /\ n = Len(str)
  /\ fail \in [0..(2*n) -> 0..(2*n) \cup {Sentinel}]
  /\ matchIdx \in 0..(2*n) \cup {Sentinel}
  /\ i \in 1..(2*n)
  /\ best \in 0..(n - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateBest", "followFail",
              "postComp", "increment", "done"}

Init ==
  /\ str \in CHARACTERSET
  /\ n = Len(str)
  /\ fail = [j \in 0..(2*n) |-> Sentinel]
  /\ matchIdx = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "outerCheck"

OuterCheck(i, n) == i < (2 * n)

Lookup ==
  /\ pc = "outerCheck"
  /\ OuterCheck(i, n)
  /\ matchIdx' = fail[(i + best) % n]
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, n, fail, i, best>>

InnerLoop ==
  /\ pc = "lookup"
  /\ str[(i + best) % n] # str[matchIdx % n]
  /\ matchIdx # Sentinel
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, n, fail, matchIdx, i, best>>

UpdateBest ==
  /\ pc = "innerLoop"
  /\ str[(i + best) % n] < str[matchIdx % n]
  /\ best' = i
  /\ pc' = "followFail"
  /\ UNCHANGED <<str, n, fail, matchIdx, i>>

FollowFail ==
  /\ pc = "innerLoop"
  /\ matchIdx # Sentinel
  /\ matchIdx' = fail[matchIdx]
  /\ pc' = "lookup"
  /\ UNCHANGED <<str, n, fail, i, best>>

PostComp ==
  /\ pc = "innerLoop"
  /\ matchIdx = Sentinel
  /\ pc' = "postComp"
  /\ UNCHANGED <<str, n, fail, matchIdx, i, best>>

UpdateAfterPostComp ==
  /\ pc = "postComp"
  /\ IF str[(i + best) % n] < str[matchIdx % n]
       THEN best' = i
       ELSE best' = best
  /\ fail' = [fail EXCEPT ![(i + best) % n] =
                       IF matchIdx = Sentinel THEN Sentinel ELSE matchIdx + 1]
  /\ pc' = "increment"
  /\ UNCHANGED <<str, n, matchIdx, i>>

Increment ==
  /\ pc = "increment"
  /\ i' = i + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<str, n, fail, matchIdx, best>>

Done ==
  /\ pc = "outerCheck"
  /\ ~OuterCheck(i, n)
  /\ pc' = "done"
  /\ UNCHANGED <<str, n, fail, matchIdx, i, best>>

Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ Lookup \/ InnerLoop \/ UpdateBest \/ FollowFail \/ PostComp
  \/ UpdateAfterPostComp \/ Increment \/ Done \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(InnerLoop)
        /\ WF_vars(FollowFail) /\ WF_vars(PostComp) /\ WF_vars(Increment)

Correctness ==
  /\ (pc = "done") => (best = 0)
  /\ (pc = "done") => \A k \in 0..(n - 1) :
       LET rot(a) == SubSeq(str, a, a + n - 1) IN rot(best) <= rot(k)

\* Progress measure: each outer loop iteration advances i, and a rotating
\* index that always moves forward guarantees termination.
Termination == <>(pc = "done")

====