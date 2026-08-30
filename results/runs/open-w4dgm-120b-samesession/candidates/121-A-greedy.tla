---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Zero-indexed sequences over a finite character set, with a sentinel value
\* for "undefined" that is outside the character set.
\* The algorithm is a deterministic linear-time scan over a doubled string.
\* The invariant is a pair of lexicographic comparisons: the chosen rotation
\* is <= every other rotation, and among equal rotations it has the smallest shift.

ASSUME CharacterSet \subseteq Nat

Sentinel == 0
MaxLen == 2
MaxLoop == 2 * MaxLen

VARIABLES str, n, fail, patIdx, loop, best, pc

vars == <<str, n, fail, patIdx, loop, best, pc>>

TypeInvariant ==
    /\ str \in [0..MaxLen -> CharacterSet]
    /\ n \in 0..MaxLen
    /\ fail \in [0..MaxLoop -> 0..MaxLoop]
    /\ patIdx \in 0..MaxLoop
    /\ loop \in 0..MaxLoop
    /\ best \in 0..MaxLen
    /\ pc \in {"outer", "lookup", "inner", "post", "done"}

Init ==
    /\ \E s \in [0..MaxLen -> CharacterSet] : str = s
    /\ n = Len(str)
    /\ fail = [i \in 0..MaxLoop |-> Sentinel]
    /\ patIdx = Sentinel
    /\ loop = 1
    /\ best = 0
    /\ pc = "outer"

Outer ==
    /\ pc = "outer"
    /\ IF loop < MaxLoop
       THEN pc' = "lookup"
       ELSE pc' = "done"
    /\ UNCHANGED <<str, n, fail, patIdx, loop, best>>

Lookup ==
    /\ pc = "lookup"
    /\ patIdx' = fail[loop - best]
    /\ pc' = "inner"
    /\ UNCHANGED <<str, n, fail, loop, best>>

\* The inner loop walks the failure chain; the loop guard is the guard, not
\* a separate IF, so the guard and the body are the same expression.
Inner ==
    /\ pc = "inner"
    /\ /\ str[loop % n] # str[(best + patIdx) % n]
       /\ patIdx # Sentinel
    /\ pc' = "post"
    /\ UNCHANGED <<str, n, fail, patIdx, loop, best>>

UpdateBest ==
    /\ pc = "inner"
    /\ str[loop % n] < str[(best + patIdx) % n]
    /\ best' = (loop - patIdx) % n
    /\ UNCHANGED <<str, n, fail, patIdx, loop, pc>>

FollowFail ==
    /\ pc = "inner"
    /\ patIdx' = fail[patIdx]
    /\ UNCHANGED <<str, n, fail, loop, best, pc>>

Post ==
    /\ pc = "post"
    /\ /\ str[loop % n] # str[(best + patIdx) % n]
       /\ patIdx = Sentinel
    /\ IF str[loop % n] < str[(best + patIdx) % n]
       THEN best' = (loop - patIdx) % n
       ELSE best' = best
    /\ fail' = [fail EXCEPT ![loop - best] =
                  IF str[loop % n] = str[(best + patIdx) % n]
                  THEN Sentinel
                  ELSE patIdx + 1]
    /\ pc' = "outer"
    /\ UNCHANGED <<str, n, patIdx, loop>>

Next ==
    \/ Outer
    \/ Lookup
    \/ Inner
    \/ UpdateBest
    \/ FollowFail
    \/ Post
    \/ (pc = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Outer) /\ WF_vars(Lookup)
        /\ WF_vars(Inner) /\ WF_vars(UpdateBest) /\ WF_vars(FollowFail) /\ WF_vars(Post)

\* Lexicographic comparison of two rotations of the same string.
RotLessOrEqual(i, j) ==
    \E k \in 0..n-1 :
        /\ \A m \in 0..(k - 1) : str[(i + m) % n] = str[(j + m) % n]
        /\ str[(i + k) % n] <= str[(j + k) % n]

Correctness ==
    /\ n > 0
    /\ \A j \in 0..(n - 1) : RotLessOrEqual(best, j)
    /\ \A j \in 0..(n - 1) :
         (RotLessOrEqual(best, j) /\ RotLessOrEqual(j, best)) => best <= j

Termination == <>(pc = "done")

====