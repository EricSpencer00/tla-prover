---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Sentinel value used for “undefined” entries in the failure function
SENTINEL == -1

VARIABLES str, n, f, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
CharAt(pos) == 
    (* 1‑indexed access to the sequence `str` using zero‑based modular index *)
    str[ ((pos) % n) + 1 ]

Rot(offset) == 
    [j \in 1..n |-> CharAt(offset + (j-1))]

LexLe(off1, off2) == 
    \A j \in 1..n :
        ( \A k \in 1..(j-1) : Rot(off1)[k] = Rot(off2)[k] ) => Rot(off1)[j] <= Rot(off2)[j]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ f = [j \in 0..(2*n) |-> SENTINEL]
    /\ k = SENTINEL
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2 * n
       THEN /\ pc' = "Lookup"
            /\ UNCHANGED <<str, n, f, k, best, i>>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<str, n, f, k, best, i>>

Lookup ==
    /\ pc = "Lookup"
    /\ (* Retrieve failure function entry for the current position relative
          to the current best offset.  The exact index is abstracted as `i`. *)
    /\ k' = f[i]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, n, f, best, i>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ LET c1 == CharAt(i) 
           c2 == CharAt(best + i) IN
       IF c1 = c2 THEN
           /\ pc' = "PostComparison"
           /\ UNCHANGED <<str, n, f, k, best, i>>
       ELSE
           IF c1 # c2 /\ k # SENTINEL THEN
               /\ pc' = "InnerLoop"      \* continue inner comparison
               /\ UNCHANGED <<str, n, f, k, best, i>>
           ELSE
               /\ pc' = "PostComparison"
               /\ UNCHANGED <<str, n, f, k, best, i>>

PostComparison ==
    /\ pc = "PostComparison"
    /\ LET c1 == CharAt(i) 
           c2 == CharAt(best + i) IN
       /\ IF c1 # c2 /\ k = SENTINEL THEN
              /\ IF c1 < c2 THEN best' = i ELSE best' = best
          ELSE IF c1 # c2 /\ k # SENTINEL THEN
              /\ best' = best
          ELSE 
              /\ best' = best
       /\ f' = [f EXCEPT ![i] = IF c1 = c2 THEN SENTINEL ELSE (k + 1)]
       /\ pc' = "Inc"
       /\ UNCHANGED <<str, n, k, i>>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, n, f, k, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, f, k, i, best, pc>>

\* Stuttering after termination
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, f, k, i, best, pc>>

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostComparison
    \/ Inc
    \/ Done
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, f, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ f \in [0..(2*n) -> Int]
    /\ (k = SENTINEL) \/ (k \in 0..(2*n))
    /\ i \in 1..(2*n + 1)
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComparison", "Inc", "Done"}

Correctness ==
    /\ pc = "Done"
    /\ \A shift \in 0..(n-1) : LexLe(best, shift)

=============================================================================