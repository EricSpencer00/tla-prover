---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxChar

\* Import a finite character set definition
INSTANCE ZSequences WITH MaxChar <- MaxChar

\* Sentinel value for undefined entries in the failure function
Sentinel == -1

VARIABLES str, n, f, k, i, best, pc

\* ---------- Helper definitions ----------
\* Zero‑indexed string is a function from 0..n-1 to CharacterSet
String == [0..n-1 -> CharacterSet]

\* Rotation of the string by offset (modulo n)
RotSeq(offset) ==
  [j \in 0..n-1 |-> str[(offset + j) % n]]

\* Lexicographic less‑or‑equal between two zero‑indexed sequences of length n
LexLe(a, b) ==
  \A j \in 0..n-1 :
    ( \A m \in 0..j-1 : a[m] = b[m] ) => a[j] <= b[j]

\* Equality of two zero‑indexed sequences of length n
LexEq(a, b) ==
  \A j \in 0..n-1 : a[j] = b[j]

\* The minimal rotation offset (chosen deterministically via CHOOSE)
MinimalRotation ==
  CHOOSE off \in 0..n-1 :
    \A o \in 0..n-1 : LexLe(RotSeq(off), RotSeq(o))

\* ---------- Invariant ----------
TypeInvariant ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in String
  /\ f \in [0..2*n-1 -> (Nat \cup {Sentinel})]
  /\ k \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck", "FailureLookup", "InnerLoop",
             "PostComparison", "Increment", "Done"}

\* ---------- Correctness property ----------
Correctness ==
  /\ pc = "Done"
  /\ \A offset \in 0..n-1 :
        /\ LexLe(RotSeq(best), RotSeq(offset))
        /\ (LexEq(RotSeq(best), RotSeq(offset)) => best <= offset)

\* ---------- Initial state ----------
Init ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in String
  /\ f = [j \in 0..2*n-1 |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ---------- Actions ----------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*n
        THEN /\ pc' = "FailureLookup"
             /\ UNCHANGED <<str, n, f, k, i, best>>
        ELSE /\ pc' = "Done"
             /\ best' = MinimalRotation
             /\ UNCHANGED <<str, n, f, k, i>>

FailureLookup ==
  /\ pc = "FailureLookup"
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, f, k, i, best>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ pc' = "PostComparison"
  /\ UNCHANGED <<str, n, f, k, i, best>>

PostComparison ==
  /\ pc = "PostComparison"
  /\ pc' = "Increment"
  /\ UNCHANGED <<str, n, f, k, i, best>>

Increment ==
  /\ pc = "Increment"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, f, k, best>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best, pc>>

Next ==
  \/ OuterCheck
  \/ FailureLookup
  \/ InnerLoop
  \/ PostComparison
  \/ Increment
  \/ Stutter

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<str, n, f, k, i, best, pc>>

\* ---------- Invariants for the model checker ----------
INVARIANT TypeInvariant, Correctness

====