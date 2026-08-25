---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Finite character set definition (replaces Nat from Naturals for the
\* ZSequences module as required by the .cfg file).  Keep EXTENDS Naturals
\* but do NOT declare or redefine Nat.
\* ----------------------------------------------------------------------
CONSTANT CharacterSet

\* Provide the replacement for Nat used by ZSequences
ZSequences!CharacterSet == CharacterSet

\* Sentinel value for undefined failure function entries and pattern index
Sentinel == -1

\* State variables
VARIABLES str, n, fail, k, i, best, pc

\* Helper definitions
CharAt(off, offset) ==
    IF n = 0 THEN Sentinel
    ELSE str[(off + offset) % n]

LessThanRot(off1, off2) ==
    \E k \in 0..(n-1) :
        (\A j \in 0..(k-1) : CharAt(off1, j) = CharAt(off2, j)) /\
        CharAt(off1, k) < CharAt(off2, k)

EqualRot(off1, off2) ==
    \A j \in 0..(n-1) : CharAt(off1, j) = CharAt(off2, j)

\* Initial state
Init ==
    /\ n \in Nat
    /\ n > 0
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ fail = [j \in 0..(2*n) |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* Actions
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2 * n
          THEN /\ pc' = "Compare"
               /\ UNCHANGED <<str, n, fail, k, i, best>>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<str, n, fail, k, i, best>>

Compare ==
    /\ pc = "Compare"
    /\ LET off == i % n IN
          IF LessThanRot(off, best)
             THEN best' = off
             ELSE best' = best
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<str, n, fail, k>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

Next ==
    \/ OuterCheck
    \/ Compare
    \/ Done

\* Specification
Spec == Init /\ [][Next]_<<str, n, fail, k, i, best, pc>>

\* Type invariant
TypeInvariant ==
    /\ n \in Nat
    /\ n > 0
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ fail \in [0..(2*n) -> Int]
    /\ \A j \in 0..(2*n) : fail[j] = Sentinel \/ (fail[j] \in 0..(2*n))
    /\ k \in Int
    /\ i \in Nat
    /\ best \in 0..(n-1)
    /\ pc \in {"OuterCheck", "Compare", "Done"}

\* Correctness property
Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..(n-1) : ~LessThanRot(off, best)   \* no rotation is strictly smaller
    /\ \A off \in 0..(n-1) :
          (EqualRot(off, best) => best <= off)        \* tie‑break on smallest offset

====