---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\*--------------------------------------------------------------------
\* Constants
\*--------------------------------------------------------------------
CONSTANTS
    CharacterSetSet            \* finite subset of Nat (provided by the .cfg)

\*--------------------------------------------------------------------
\* Derived operator required by the configuration
\*--------------------------------------------------------------------
\* This definition replaces the Nat type from Naturals with a finite
\* character set so that the model is checkable.
CharacterSet == CharacterSetSet

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES
    str,    \* input string: function 0..n-1 -> CharacterSet
    n,      \* length of the string (Nat)
    f,      \* failure function array 0..2*n-1 -> Int (sentinel = -1)
    p,      \* pattern‑match index (used as inner compare counter)
    i,      \* outer loop counter (0..2*n)
    best,   \* best rotation offset (0..n-1)
    pc      \* program counter (labels of the algorithm)

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Sentinel == -1

\* Zero‑based indexing modulo the length of the string
Idx(i) == i % n

\* The rotation of the input string that starts at offset o
Rotation(o) == [k \in 0..(n-1) |-> str[Idx(o + k)]]

\* Lexicographic less‑or‑equal between two rotations of equal length
LexLe(s, t) ==
    \* there exists a first position where they differ (or none)
    \E k \in 0..n :
        (\A m \in 0..(k-1) : s[m] = t[m]) /\ (k = n \/ s[k] <= t[k])

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ n \in Nat
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ f = [j \in 0..(2*n-1) |-> Sentinel]
    /\ p = Sentinel
    /\ i = 0
    /\ best = 0
    /\ pc = "OuterCheck"

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2 * n
          THEN pc' = "Lookup"
          ELSE pc' = "Done"
    /\ UNCHANGED <<str, n, f, p, i, best>>

Lookup ==
    /\ pc = "Lookup"
    /\ (* retrieve failure function value for the current position *)
       p' = f[Idx(best + i)]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, n, f, i, best>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ LET cur  == str[Idx(i)]
           cand == str[Idx(best + i)]
       IN
          IF cur = cand
              THEN /\ p' = p + 1
                 /\ pc' = "InnerLoop"
          ELSE IF cur < cand
              THEN /\ best' = Idx(i)
                 /\ p' = Sentinel
                 /\ pc' = "PostComp"
          ELSE /\ p' = Sentinel
                 /\ pc' = "PostComp"
    /\ UNCHANGED <<str, n, f, i>>

PostComp ==
    /\ pc = "PostComp"
    /\ (* update failure function entry based on the outcome of the comparison *)
       IF p = Sentinel
          THEN f' = [f EXCEPT ![Idx(best + i)] = Sentinel]
          ELSE f' = [f EXCEPT ![Idx(best + i)] = p + 1]
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, n, p, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, f, p, i, best, pc>>

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostComp
    \/ Done

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, f, p, i, best, pc>>

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeInvariant ==
    /\ n \in Nat
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ f \in [0..(2*n-1) -> Int]
    /\ \A j \in DOMAIN f : f[j] = Sentinel \/ (f[j] \in 0..(2*n-1))
    /\ p = Sentinel \/ p \in 0..(2*n-1)
    /\ i \in 0..(2*n)
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Done"}

Correctness ==
    /\ pc = "Done"
    /\ \A j \in 0..(n-1) : LexLe(Rotation(best), Rotation(j))

\*--------------------------------------------------------------------
\* Assumptions about the character set (finite)
\*--------------------------------------------------------------------
ASSUME CharacterSetSet \subseteq Nat

====