---- MODULE LeastCircularSubstring ----
EXTENDS Naturals

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Sentinel value used to denote "undefined" entries in the failure array.
\* ----------------------------------------------------------------------
SENTINEL == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, pi, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx(pos) == 
    IF n = 0 THEN 0 ELSE (pos % n)

CharAt(pos) == 
    IF n = 0 THEN 0 ELSE str[Idx(pos)]

Rot(off) == 
    [k \in 0..n-1 |-> CharAt(off + k)]

\* Lexicographic less-or-equal between two zero‑indexed sequences.
LexLe(s, t) == 
    \A k \in 0..n-1 : 
        \A m \in 0..k-1 : s[m] = t[m] 
        => s[k] <= t[k]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ n \in Nat
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail = [j \in 0..2*n-1 |-> SENTINEL]
    /\ pi = SENTINEL
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions corresponding to the labeled steps of Booth's algorithm
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2 * n 
          THEN pc' = "Lookup"
          ELSE pc' = "Done"
    /\ UNCHANGED <<str, n, fail, pi, i, best>>

Lookup ==
    /\ pc = "Lookup"
    /\ \* index in the failure array is relative to the current best offset
       idx == (i + best) % n
    /\ pi' = fail[idx]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, n, fail, i, best>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ \* Compare characters at positions i and best+pi+1 (mod n)
       cur  == CharAt(i)
       cand == CharAt(best + pi + 1)
    /\ IF cur = cand THEN
          /\ pi' = pi + 1
          /\ pc' = "InnerLoop"
      ELSE IF pi # SENTINEL THEN
          /\ pi' = fail[(best + pi) % n]
          /\ pc' = "InnerLoop"
      ELSE
          /\ pc' = "PostComp"
    /\ UNCHANGED <<str, n, fail, i, best>>

PostComp ==
    /\ pc = "PostComp"
    /\ cur  == CharAt(i)
       cand == CharAt(best + pi + 1)
    /\ IF cur # cand /\ pi = SENTINEL THEN
          /\ IF cur < cand THEN best' = i - (pi + 1) ELSE best' = best
          /\ fail[(i + best) % n] = SENTINEL
       ELSE
          /\ IF cur < cand THEN best' = i - (pi + 1) ELSE best' = best
          /\ fail[(i + best) % n] = pi + 1
    /\ pc' = "Inc"
    /\ UNCHANGED <<str, n, pi, i>>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, n, fail, pi, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, fail, pi, i, best>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, fail, pi, i, best>>

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostComp
    \/ Inc
    \/ Done
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<str, n, fail, pi, i, best, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ n \in Nat
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail \in [0..2*n-1 -> (Nat \cup {SENTINEL})]
    /\ pi \in Nat \cup {SENTINEL}
    /\ i \in Nat
    /\ best \in 0..(IF n = 0 THEN 0 ELSE n-1)
    /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Inc", "Done"}

\* ----------------------------------------------------------------------
\* Correctness property: upon termination, best denotes a lexicographically
\* minimal rotation of the input string.
\* ----------------------------------------------------------------------
Correctness ==
    /\ pc = "Done"
    /\ best \in 0..(IF n = 0 THEN 0 ELSE n-1)
    /\ \A j \in 0..(IF n = 0 THEN 0 ELSE n-1) : LexLe(Rot(best), Rot(j))

====