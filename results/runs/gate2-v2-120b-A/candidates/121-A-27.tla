---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (set in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT CharacterSet
CONSTANT Nat

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Char == CharacterSet

Sentinel == -1

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    s,          \* input string (sequence of Char), zero-indexed
    n,          \* length of s
    f,          \* failure function array, indexed 0..2*n
    p,          \* pattern-match index (or Sentinel)
    i,          \* outer loop counter, runs 1..2*n
    best,       \* best rotation offset, 0..n-1
    pc          \* program counter (one of the labeled steps)

\* ----------------------------------------------------------------------
\* Type predicate (used in the TypeInvariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ s \in Seq(Char)
    /\ n = Len(s)
    /\ f \in [0..2*n -> (Sentinel .. n)]
    /\ p \in {Sentinel} \cup 0..n
    /\ i \in 0..2*n
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterCheck", "FailureLookup", "InnerLoop",
               "UpdateBestIfLess", "FollowFailure", "PostComparison",
               "Increment", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ s \in Seq(Char)
    /\ n = Len(s)
    /\ f = [j \in 0..2*n |-> Sentinel]
    /\ p = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Helper functions for modulo indexing (circular access)
\* ----------------------------------------------------------------------
CharAt(pos) == s[ (pos % n) + 1 ]   \* +1 because TLC sequences are 1‑indexed

\* ----------------------------------------------------------------------
\* Actions corresponding to the labeled steps
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2*n + 1
          THEN pc' = "FailureLookup"
          ELSE pc' = "Done"
    /\ UNCHANGED << s, n, f, p, i, best >>

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ p' = f[ i - best ]          \* lookup relative to best offset
    /\ pc' = "InnerLoop"
    /\ UNCHANGED << s, n, f, i, best >>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ LET curChar == CharAt(i)
           candPos == best + p
           candChar == IF p = Sentinel THEN "" ELSE CharAt(candPos)
       IN
       IF p # Sentinel /\ curChar = candChar
          THEN /\ p' = p + 1
               /\ pc' = "InnerLoop"    \* stay in inner loop
          ELSE pc' = "PostComparison"
    /\ UNCHANGED << s, n, f, i, best, p >>

UpdateBestIfLess ==
    /\ pc = "UpdateBestIfLess"
    /\ CurChar == CharAt(i)
    /\ CandChar == CharAt(best + p)
    /\ (CurChar < CandChar) => best' = i % n
    /\ pc' = "FollowFailure"
    /\ UNCHANGED << s, n, f, i, p >>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ p' = f[ (i - best) - 1 ]   \* follow failure link for next iteration
    /\ pc' = "Increment"
    /\ UNCHANGED << s, n, f, i, best >>

PostComparison ==
    /\ pc = "PostComparison"
    /\ LET curChar == CharAt(i)
           candPos == best + p
           candChar == IF p = Sentinel THEN "" ELSE CharAt(candPos)
       IN
       IF curChar # candChar /\ p = Sentinel
          THEN /\ IF curChar < candChar THEN best' = i % n
               /\ f' = [f EXCEPT ![i - best] = IF curChar # candChar
                                              THEN Sentinel
                                              ELSE p + 1]
               /\ pc' = "Increment"
          ELSE /\ pc' = "Increment"
    /\ UNCHANGED << s, n, p, i >>

Increment ==
    /\ pc = "Increment"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED << s, n, f, p, best >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED << s, n, f, p, i, best, pc >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ OuterCheck
    \/ FailureLookup
    \/ InnerLoop
    \/ UpdateBestIfLess
    \/ FollowFailure
    \/ PostComparison
    \/ Increment
    \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<s, n, f, p, i, best, pc>>

\* ----------------------------------------------------------------------
\* Safety invariants required by the .cfg file
\* ----------------------------------------------------------------------
TypeInvariant == TypeOK

\* Rotation of a string by offset k (0‑based)
Rotate(s, k) ==
    IF Len(s) = 0
       THEN <<>>
       ELSE
          LET m == Len(s) IN
          [j \in 1..m |-> s[ ((j-1 + k) % m) + 1 ]]

\* Lexicographic order on sequences (TLC's default order works for Char)
Correctness ==
    /\ best \in 0..(n-1)
    /\ \A k \in 0..(n-1) :
          Rotate(s, best) <= Rotate(s, k)

\* ----------------------------------------------------------------------
\* Termination (optional, not referenced in the .cfg but kept for completeness)
\* ----------------------------------------------------------------------
Termination == <>[] (pc = "Done")

=============================================================================