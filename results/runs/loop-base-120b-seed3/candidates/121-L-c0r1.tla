---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* Finite version of Nat for model checking (replaces Nat from Naturals)
\* This definition satisfies the requirement [ZSequences]CharacterSet
\* ----------------------------------------------------------------------
[ZSequences]CharacterSet == 0..10  \* adjust upper bound as needed for the model

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* Length of a zero‑indexed sequence (domain 0..n-1)
SeqLen(s) == IF DOMAIN s = {} THEN 0 ELSE Max(DOMAIN s) + 1

\* Rotation of the string by offset o (zero‑indexed)
Rot(o) == [j \in 0..n-1 |-> str[(o + j) % n]]

\* Lexicographic less‑or‑equal between two zero‑indexed sequences of length n
LexLe(s, t) ==
  \E m \in 0..n :
    (\A j \in 0..m-1 : s[j] = t[j]) /\ (m = n \/ s[m] <= t[m])

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ n >= 0
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail = [j \in 0..2*n |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions for each program‑counter label
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
       THEN pc' = "Lookup"
       ELSE pc' = "Done"
  /\ UNCHANGED << str, n, fail, k, i, best >>

Lookup ==
  /\ pc = "Lookup"
  /\ (* retrieve failure function value for position i relative to best *)
     k' = fail[(i - best) % (2 * n + 1)]  \* index may exceed 2*n, safe due to domain
  /\ pc' = "InnerLoop"
  /\ UNCHANGED << str, n, fail, i, best >>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ LET cur  == str[i % n] 
         cand == str[(best + k + 1) % n] IN
     IF cur = cand
        THEN /\ k' = k + 1
             /\ pc' = "InnerLoop"
        ELSE IF cur < cand
                THEN /\ best' = i - k - 1
                     /\ k' = Sentinel
                     /\ pc' = "PostComp"
                ELSE /\ k' = Sentinel
                     /\ pc' = "PostComp"
  /\ UNCHANGED << str, n, fail, i >>

PostComp ==
  /\ pc = "PostComp"
  /\ LET cur  == str[i % n] 
         cand == str[(best + k + 1) % n] IN
     IF cur # cand /\ k = Sentinel
        THEN /\ IF cur < cand THEN best' = i - k - 1 ELSE UNCHANGED best
             /\ fail[(i - best) % (2 * n + 1)]' = Sentinel
        ELSE /\ fail[(i - best) % (2 * n + 1)]' = k + 1
  /\ pc' = "Inc"
  /\ UNCHANGED << str, n, i >>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << str, n, fail, k, best >>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED << str, n, fail, k, i, best, pc >>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED << str, n, fail, k, i, best, pc >>

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
Spec == Init /\ [][Next]_<< str, n, fail, k, i, best, pc >>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n = SeqLen(str)
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n -> Nat \cup {Sentinel}]
  /\ k \in Nat \cup {Sentinel}
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Inc", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A o \in 0..n-1 : LexLe(Rot(best), Rot(o))

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS == TypeInvariant, Correctness

====