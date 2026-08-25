---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\*--------------------------------------------------------------------
\* Constants
\*--------------------------------------------------------------------
CONSTANTS CharacterSet            \* Finite set of characters, supplied by the model

\*--------------------------------------------------------------------
\* Finite version of Nat for substitution (right‑hand side of [ZSequences]CharacterSet)
\*--------------------------------------------------------------------
ZSequences_CharacterSet == 0..MaxChar
CONSTANT MaxChar

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES str,               \* input string as a function 0..n-1 -> CharacterSet
          n,                 \* length of the string (positive)
          fail,              \* failure function array 0..2*n -> Nat \cup {sentinel}
          k,                 \* pattern‑match index (sentinel or Nat)
          i,                 \* outer loop counter (1..2*n)
          best,              \* best rotation offset (0..n-1)
          pc                 \* program counter (label of the step)

\*--------------------------------------------------------------------
\* Sentinels and helper sets
\*--------------------------------------------------------------------
sentinel == -1

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeInvariant ==
    /\ n \in Nat \setminus {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail \in [0..2*n -> (Nat \cup {sentinel})]
    /\ k \in (Nat \cup {sentinel})
    /\ i \in 1..2*n
    /\ best \in 0..n-1
    /\ pc \in {"OuterCheck","Lookup","InnerLoop","UpdateBest","FollowFail",
               "PostComp","Inc","Done"}

\*--------------------------------------------------------------------
\* Rotation of the string by offset o
\*--------------------------------------------------------------------
Rotation(o) == [j \in 0..n-1 |-> str[(o + j) % n]]

\*--------------------------------------------------------------------
\* Lexicographic less‑or‑equal on two rotations
\*--------------------------------------------------------------------
LexLeq(s1, s2) ==
    \A j \in 0..n-1 :
        (\A k \in 0..j-1 : s1[k] = s2[k]) => s1[j] <= s2[j]

\*--------------------------------------------------------------------
\* Correctness property (minimal rotation)
\*--------------------------------------------------------------------
Correctness ==
    \A o \in 0..n-1 : LexLeq(Rotation(best), Rotation(o))

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ n \in Nat \setminus {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail = [j \in 0..2*n |-> sentinel]
    /\ k = sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\*--------------------------------------------------------------------
\* Transition relation (captures the algorithmic steps)
\*--------------------------------------------------------------------
Next ==
    \/ /\ pc = "OuterCheck"
       /\ IF i < 2*n
          THEN /\ pc' = "Lookup"
               /\ UNCHANGED <<str, n, fail, k, i, best>>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<str, n, fail, k, i, best>>
    \/ /\ pc = "Lookup"
       /\ \* retrieve failure function value for position (i-1)
          let pos == (i-1) % n in
          k' = fail[pos]
       /\ pc' = "InnerLoop"
       /\ UNCHANGED <<str, n, fail, i, best>>
    \/ /\ pc = "InnerLoop"
       /\ let curChar  == str[i % n] in
          let candChar == str[(best + k) % n] in
          /\ IF curChar = candChar
             THEN /\ k' = k + 1
                  /\ pc' = "InnerLoop"
             ELSE /\ IF k # sentinel
                  THEN /\ k' = fail[k]
                       /\ pc' = "InnerLoop"
                  ELSE /\ pc' = "PostComp"
                       /\ k' = k
       /\ UNCHANGED <<str, n, fail, i, best>>
    \/ /\ pc = "PostComp"
       /\ let curChar  == str[i % n] in
          let candChar == str[(best + k) % n] in
          /\ IF curChar # candChar
             THEN /\ IF curChar < candChar THEN best' = i % n ELSE best' = best
                  /\ fail[i % n] = sentinel
                  /\ pc' = "Inc"
             ELSE /\ IF curChar < candChar
                  THEN best' = i % n
                  ELSE best' = best
                  /\ fail[i % n] = k + 1
                  /\ pc' = "Inc"
       /\ UNCHANGED <<str, n, k>>
    \/ /\ pc = "Inc"
       /\ i' = i + 1
       /\ pc' = "OuterCheck"
       /\ UNCHANGED <<str, n, fail, k, best>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, fail, k, i, best, pc>>

\*--------------------------------------------------------------------
\* Theorems (optional, can be used by TLC)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []Correctness

====