---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT CharacterSet      \* the finite alphabet (set of natural numbers)
CONSTANT MaxChar           \* upper bound for the alphabet (inclusive)

\* The cfg will assign a value to CharacterSet; we constrain it here.
ASSUME CharacterSet = 0..MaxChar
ASSUME MaxChar \in Nat

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES str,               \* input string: function 0..n-1 -> CharacterSet
          n,                 \* length of the input string
          fail,              \* failure function array: 0..2*n-1 -> NatUndef
          k,                 \* pattern‑match index (may be sentinel)
          i,                 \* outer loop counter (1 .. 2*n)
          best,              \* current best rotation offset (0 .. n-1)
          pc                 \* program counter (label of the step)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1               \* value meaning “undefined”

NatUndef == Nat \cup {Sentinel}

\* Rotation of a string by offset `off`.  Represented as a sequence
\* of length `n` whose j‑th element (1‑based) is the character at
\* position (off + (j-1)) mod n of `str`.
Rotation(s, off) ==
  [j \in 1..n |-> s[(off + (j-1)) % n]]

\* Lexicographic ≤ on two sequences of equal length.
LexLe(s1, s2) ==
  \A j \in 1..n :
    (s1[j] = s2[j]) \/ 
    (s1[j] < s2[j] /\ \A k \in 1..(j-1) : s1[k] = s2[k])

\* The set of all possible program‑counter values.
PCValues == {"OuterCheck", "Lookup", "InnerLoop", "PostComparison",
             "Increment", "Done", "Stutter"}

\* The tuple of all variables for state‑level actions.
vars == <<str, n, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail = [j \in 0..(2*n-1) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions for each labelled step
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*n
        THEN pc' = "Lookup"
        ELSE pc' = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[i]          \* retrieve failure function entry for position i
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, i, best>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ LET curChar == str[i % n] IN
     IF k = Sentinel
        THEN pc' = "PostComparison"
        ELSE
          LET candChar == str[(best + k) % n] IN
             IF curChar = candChar
                THEN  \* characters match – extend the current match
                      k' = k + 1
                      pc' = "InnerLoop"
                ELSE  \* characters differ – decide whether to update best
                      IF curChar < candChar
                         THEN best' = i % n
                         ELSE UNCHANGED best
                      /\ k' = Sentinel
                      /\ pc' = "PostComparison"
  /\ UNCHANGED <<str, n, fail, i>>

PostComparison ==
  /\ pc = "PostComparison"
  /\ LET curChar == str[i % n] IN
     LET candChar == 
        IF best + k \in 0..(n-1) THEN str[(best + k) % n] ELSE curChar
     IN
        IF curChar # candChar
           THEN
               IF curChar < candChar
                  THEN best' = i % n
                  ELSE UNCHANGED best
               /\ fail' = [fail EXCEPT ![i] = Sentinel]
           ELSE
               /\ best' = best
               /\ fail' = [fail EXCEPT ![i] = k + 1]
  /\ pc' = "Increment"
  /\ UNCHANGED <<str, n, k, i>>

Increment ==
  /\ pc = "Increment"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, k, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Stutter ==
  /\ pc = "Stutter"
  /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ PostComparison
  \/ Increment
  \/ Done
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..(2*n-1) -> NatUndef]
  /\ k \in NatUndef
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in PCValues

\* ----------------------------------------------------------------------
\* Correctness invariant (lexicographically minimal rotation)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..(n-1) :
        LexLe(Rotation(str, best), Rotation(str, off))

\* ----------------------------------------------------------------------
\* Properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvariant, Correctness
SPECIFICATION == Spec

====