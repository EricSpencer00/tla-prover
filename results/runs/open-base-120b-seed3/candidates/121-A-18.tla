---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Sentinel value for undefined entries (outside CharacterSet and Nat)
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Length of a zero‑indexed sequence represented as a function
Len(s) == Cardinality(DOMAIN s)

\* Circular index modulo n
Idx(j) == j % n

\* Rotation of the string starting at offset o
Rotation(o) == [j \in 0..n-1 |-> str[Idx(o + j)]]

\* Lexicographic less‑or‑equal between two rotations
LexLe(o1, o2) ==
  \E m \in 0..n :
    /\ \A j \in 0..m-1 : Rotation(o1)[j] = Rotation(o2)[j]
    /\ (m = n \/ Rotation(o1)[m] <= Rotation(o2)[m])

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  \E m \in Nat :
    /\ m > 0
    /\ str \in [0..m-1 -> CharacterSet]
    /\ n = Len(str)
    /\ fail = [j \in 0..2*n-1 |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "Check"

\* ----------------------------------------------------------------------
\* Algorithm actions (one per program‑counter label)
\* ----------------------------------------------------------------------
Check ==
  /\ pc = "Check"
  /\ IF i < 2 * n THEN pc' = "Lookup"
     ELSE pc' = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ (* look up failure function for position i relative to best *)
     k' = IF i - best \in DOMAIN fail THEN fail[i - best] ELSE Sentinel
  /\ pc' = "Inner"
  /\ UNCHANGED <<str, n, fail, i, best>>

Inner ==
  /\ pc = "Inner"
  /\ let curIdx  == Idx(i)               \* index of current character
         candIdx == Idx(best + i - best) \* index of candidate character (same as curIdx)
         curChar == str[curIdx]
         candChar == str[candIdx] in
     IF curChar = candChar THEN
        (* characters equal, move to next iteration *)
        pc' = "Inc"
        /\ UNCHANGED <<k>>
     ELSE
        (* characters differ, decide next step *)
        IF k # Sentinel THEN
           (* follow failure chain *)
           pc' = "Lookup"
           /\ UNCHANGED <<k>>
        ELSE
           (* no failure, go to post‑comparison *)
           pc' = "PostComp"
           /\ UNCHANGED <<k>>
     )
  /\ UNCHANGED <<str, n, fail, i, best>>

PostComp ==
  /\ pc = "PostComp"
  /\ let curIdx  == Idx(i)
         candIdx == Idx(best + i - best)
         curChar == str[curIdx]
         candChar == str[candIdx] in
     IF curChar # candChar THEN
        (* update best if current character is smaller *)
        IF curChar < candChar THEN
           best' = Idx(i - best)      \* new best offset
        ELSE
           best' = best
        /\ fail' = [fail EXCEPT ![i - best] = Sentinel]   \* reset entry
        /\ pc' = "Inc"
     ELSE
        (* characters equal – extend match *)
        best' = best
        /\ fail' = [fail EXCEPT ![i - best] = k + 1]
        /\ pc' = "Inc"
  /\ UNCHANGED <<str, n, k, i>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "Check"
  /\ UNCHANGED <<str, n, fail, k, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

Next ==
  \/ Check
  \/ Lookup
  \/ Inner
  \/ PostComp
  \/ Inc
  \/ Done

\* ----------------------------------------------------------------------
\* Variables tuple for convenience
\* ----------------------------------------------------------------------
vars == <<str, n, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ str \in [0..n-1 -> CharacterSet]
  /\ n = Len(str)
  /\ fail \in [0..2*n-1 -> (Nat \cup {Sentinel})]
  /\ k \in Nat \cup {Sentinel}
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"Check", "Lookup", "Inner", "PostComp", "Inc", "Done"}

\* ----------------------------------------------------------------------
\* Correctness property (minimal rotation)
\* ----------------------------------------------------------------------
Correctness ==
  pc = "Done" =>
    \A shift \in 0..n-1 : LexLe(best, shift)

====