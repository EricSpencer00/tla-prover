---- MODULE LeastCircularSubstring ----
EXTENDS Integers, Sequences

CONSTANTS CharacterSet, Nat
Sentinel == -1

VARIABLES str, n, fail, matchIdx, loop, best, pc
vars == <<str, n, fail, matchIdx, loop, best, pc>>

Corpus == { s \in Seq(CharacterSet) : Len(s) <= Nat }

TypeInvariant ==
    /\ str \in Corpus
    /\ n = Len(str)
    /\ n >= 1
    /\ fail \in [0..2 * n -> 0..2 * n \cup {Sentinel}]
    /\ matchIdx \in (0..2 * n) \cup {Sentinel}
    /\ loop \in 1..2 * n
    /\ best \in 0..(n - 1)
    /\ pc \in {"outer", "lookup", "inner", "post", "done"}

Init ==
    /\ str \in Corpus
    /\ n = Len(str)
    /\ fail = [i \in 0..2 * n |-> Sentinel]
    /\ matchIdx = Sentinel
    /\ loop = 1
    /\ best = 0
    /\ pc = "outer"

\* Outer loop guard: iterate up to twice the length to unwind the circular wrap.
OuterCheck ==
    /\ pc = "outer"
    /\ IF loop < 2 * n THEN
         /\ pc' = "lookup"
       ELSE
         /\ pc' = "done"
    /\ UNCHANGED <<str, n, fail, matchIdx, loop, best>>

Lookup ==
    /\ pc = "lookup"
    /\ matchIdx' = fail[(loop - 1) + best]
    /\ pc' = "inner"
    /\ UNCHANGED <<str, n, fail, loop, best>>

\* Compare the character at the current loop position with the candidate
\* position (both taken modulo the string length), following the failure
\* chain while they differ and the chain is not exhausted.
InnerLoop ==
    /\ pc = "inner"
    /\ LET cur == str[(loop - 1) % n + 1]
           cand == str[((loop - 1) + best) % n + 1]
       IN IF cur # cand /\ matchIdx # Sentinel THEN
            /\ matchIdx' = fail[matchIdx]
            /\ UNCHANGED <<str, n, fail, loop, best>>
          ELSE
            /\ pc' = "post"
            /\ UNCHANGED <<matchIdx>>

UpdateBest ==
    /\ pc = "inner"
    /\ matchIdx # Sentinel
    /\ LET cur == str[(loop - 1) % n + 1]
           cand == str[((loop - 1) + best) % n + 1]
       IN IF cur < cand
            THEN best' = loop % n
            ELSE best' = best
    /\ UNCHANGED <<str, n, fail, matchIdx, loop, pc>>

PostComparison ==
    /\ pc = "post"
    /\ LET cur == str[(loop - 1) % n + 1]
           cand == str[((loop - 1) + best) % n + 1]
       IN /\ IF cur # cand /\ matchIdx = Sentinel /\ cur < cand
               THEN best' = loop % n
               ELSE best' = best
          /\ fail' = [fail EXCEPT ![(loop - 1) + best] =
                        IF cur # cand /\ matchIdx = Sentinel
                            THEN Sentinel
                            ELSE IF matchIdx = Sentinel THEN 0 ELSE matchIdx + 1]
    /\ matchIdx' = IF cur # cand /\ matchIdx = Sentinel
                      THEN matchIdx
                      ELSE IF matchIdx = Sentinel THEN 0 ELSE matchIdx + 1
    /\ loop' = loop + 1
    /\ pc' = "outer"

DoneStall == /\ pc = "done" /\ UNCHANGED vars

Next == OuterCheck \/ Lookup \/ InnerLoop \/ UpdateBest \/ PostComparison \/ DoneStall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck)

\* Correctness: the rotation at the best offset is no greater than any other
\* rotation of the same string, and among equal rotations it has the smallest shift.
Correctness ==
    /\ pc = "done"
    /\ \A k \in 0..(n - 1) :
         LET rot(b) == SubSeq(str, b + 1, n) @@ SubSeq(str, 1, b)
             cur == rot(best) @@ rot(best)
         IN (rot(k) @@ rot(k) # cur) \/ (k >= best)

====