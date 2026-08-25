---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, ZSequences

\* Provide the operator required by the configuration file.
\* The cfg maps [ZSequences]CharacterSet to this definition.
\* Here we define a finite character set (e.g., the numbers 0,1,2).
ZSequences!CharacterSet == 0..2

\* Alias for convenience within this module.
CharacterSet == ZSequences!CharacterSet

VARIABLES input, n, fail, k, i, best, pc

\* sentinel value used for “undefined” entries in the failure function
Sentinel == -1

\* rotation of the input string starting at offset \*off\*
Rot(off) == [j \in 0..n-1 |-> input[(off + j) % n]]

\* lexicographic less‑or‑equal between two rotations *
LexLe(off1, off2) ==
  \A j \in 0..n-1 :
    IF input[(off1 + j) % n] # input[(off2 + j) % n]
    THEN input[(off1 + j) % n] < input[(off2 + j) % n]
    ELSE TRUE

\* one of the offsets that yields a lexicographically minimal rotation *
MinimalOffset == CHOOSE off \in 0..n-1 :
                  \A o \in 0..n-1 : LexLe(off, o)

\* type invariant required by the safety properties *
TypeInvariant ==
  /\ n \in Nat
  /\ n >= 0
  /\ input \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n -> Int]
  /\ k = Sentinel \/ k \in 0..2*n
  /\ i \in 0..2*n
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck", "Lookup", "Inner", "Post", "Done"}

\* correctness property – when the algorithm terminates, *best* points to a
\* lexicographically minimal rotation *
Correctness ==
  (pc = "Done") => \A off \in 0..n-1 : LexLe(best, off)

\* initial state – nondeterministically choose a string over the character set *
Init ==
  /\ n \in Nat
  /\ n >= 0
  /\ input \in [0..n-1 -> CharacterSet]
  /\ fail = [j \in 0..2*n |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* abstract step that does nothing – models the internal loop behaviour *
Step ==
  UNCHANGED <<input, n, fail, k, i, best, pc>>

\* termination action – may only occur when *best* is a minimal offset *
Terminate ==
  /\ pc # "Done"
  /\ best = MinimalOffset
  /\ pc' = "Done"
  /\ UNCHANGED <<input, n, fail, k, i>>

Next ==
  \/ Step
  \/ Terminate

vars == <<input, n, fail, k, i, best, pc>>

Spec == Init /\ [][Next]_vars

====