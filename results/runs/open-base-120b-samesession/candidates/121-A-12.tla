---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
\* CharacterSet is a finite subset of Nat used as the alphabet.
CharacterSet == 0..9   \* a placeholder finite alphabet; the model can
                       \* override this constant via the .cfg file.

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES s,                      \* input string (sequence of characters)
          n,                      \* length of the input string
          f,                      \* failure function array: [0..2*n -> Int]
          k,                      \* pattern‑match index (sentinel = -1)
          i,                      \* outer loop counter (1 .. 2*n)
          best,                   \* best rotation offset found so far
          pc                      \* program counter (labels of steps)

vars == << s, n, f, k, i, best, pc >>

\* ----------------------------------------------------------------------
\* Sentinel value used to denote “undefined” in the failure function
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
Idx(j) == j % n                         \* index modulo the string length

CharAt(pos) == s[Idx(pos) + 1]          \* Sequences are 1‑indexed

Rotation(off) == 
    << CharAt(off + j) : j \in 0..(n-1) >>

LexLe(seq1, seq2) ==
    \A j \in 1..Len(seq1) :
        IF \A k \in 1..(j-1) : seq1[k] = seq2[k]
        THEN seq1[j] <= seq2[j]
        ELSE TRUE

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ s \in Seq(CharacterSet)
    /\ n = Len(s)
    /\ n >= 0
    /\ f \in [0..(2*n) -> Int]
    /\ \A j \in 0..(2*n) : (f[j] = Sentinel) \/ (f[j] \in 0..(2*n))
    /\ k \in Int
    /\ (k = Sentinel) \/ (k \in 0..(2*n))
    /\ i \in 1..(2*n)
    /\ best \in 0..(n-1)
    /\ pc \in {"Check","Lookup","Compare","Update","Follow","Post","Inc","Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ s \in Seq(CharacterSet)
    /\ n = Len(s)
    /\ f = [j \in 0..(2*n) |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "Check"

\* ----------------------------------------------------------------------
\* Algorithm actions (one step for each labelled part of the algorithm)
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "Check"
    /\ IF i < 2*n
       THEN /\ pc' = "Lookup"
       ELSE /\ pc' = "Done"
    /\ UNCHANGED << s, n, f, k, i, best >>

Lookup ==
    /\ pc = "Lookup"
    /\ (* retrieve failure function value for position i+best *)
       LET idx == i + best IN
          k' = f[idx]
    /\ k' = f[i + best]
    /\ k' \in Int
    /\ k' = k
    /\ pc' = "Compare"
    /\ UNCHANGED << s, n, f, i, best >>

Compare ==
    /\ pc = "Compare"
    /\ LET c1 == CharAt(i)
           c2 == CharAt(best + (k+1)) IN
       IF c1 = c2
       THEN /\ (* characters equal, extend the match *)
            k' = k + 1
            pc' = "Inc"
       ELSE IF k # Sentinel
            THEN /\ (* follow failure function *)
                 k' = f[best + k]
                 pc' = "Compare"
            ELSE /\ (* k = Sentinel and chars differ *)
                 pc' = "Post"
    /\ UNCHANGED << s, n, f, i, best >>

Update ==
    /\ pc = "Update"
    /\ LET c1 == CharAt(i)
           c2 == CharAt(best + (k+1)) IN
       IF c1 < c2
       THEN /\ best' = i
            /\ UNCHANGED << s, n, f, k, i >>
       ELSE /\ UNCHANGED << s, n, f, k, i, best >>
    /\ pc' = "Follow"

Follow ==
    /\ pc = "Follow"
    /\ k' = f[best + k]
    /\ pc' = "Post"
    /\ UNCHANGED << s, n, f, i, best >>

Post ==
    /\ pc = "Post"
    /\ LET c1 == CharAt(i)
           c2 == CharAt(best + (k+1)) IN
       IF c1 # c2
       THEN /\ IF c1 < c2 THEN best' = i ELSE UNCHANGED best
            /\ f' = [f EXCEPT ![i + best] = IF k = Sentinel THEN Sentinel
                                            ELSE k+1]
       ELSE /\ UNCHANGED << best, f >>
    /\ pc' = "Inc"
    /\ UNCHANGED << s, n, k, i >>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "Check"
    /\ UNCHANGED << s, n, f, k, best >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ Compare
    \/ Update
    \/ Follow
    \/ Post
    \/ Inc
    \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Liveness (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Correctness property: when the algorithm terminates, the rotation
\* starting at `best` is lexicographically minimal among all rotations.
\* ----------------------------------------------------------------------
Correctness ==
    (pc = "Done") => 
        \A off \in 0..(n-1) : LexLe(Rotation(best), Rotation(off))

\* ----------------------------------------------------------------------
\* The set of invariants required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANT TypeInvariant
INVARIANT Correctness

====