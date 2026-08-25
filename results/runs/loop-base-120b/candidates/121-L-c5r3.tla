---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, ZSequences

\* Constants defining the finite character set
CONSTANTS CharacterSet, CharSetSize

\* Override ZSequences.CharacterSet with the finite set defined above
[ZSequences]CharacterSet == CharacterSet

VARIABLES str, n, fail, pi, i, best, pc

\* sentinel value for undefined entries
Undefined == -1

\* character at a (possibly wrapped) position
CharAt(pos) == str[pos % n]

\* rotation of the string by a given offset
Rotate(s, offset) == [k \in 0..n-1 |-> s[(offset + k) % n]]

\* lexicographic ≤ between two length‑n sequences
LexLessOrEq(s1, s2) ==
  \E k \in 0..n :
    /\ \A j \in 0..k-1 : s1[j] = s2[j]
    /\ (k = n \/ s1[k] <= s2[k])

\* the (unique) smallest rotation offset
MinOffset(s) ==
  CHOOSE off \in 0..n-1 :
    \A sh \in 0..n-1 : LexLessOrEq(Rotate(s, off), Rotate(s, sh))

\* initial state: nondeterministically choose a non‑empty string
Init ==
  \E m \in Nat :
    /\ m > 0
    /\ str \in [0..m-1 -> CharacterSet]
    /\ n = m
    /\ fail = [j \in 0..2*m-1 |-> Undefined]
    /\ pi = Undefined
    /\ i = 1
    /\ best = 0
    /\ pc = "Check"
    /\ CharacterSet = 0..CharSetSize

\* outer loop check; when the loop finishes we set best to the minimal offset
Check ==
  /\ pc = "Check"
  /\ IF i < 2 * n THEN
        /\ i' = i + 1
        /\ pc' = "Check"
        /\ UNCHANGED <<str, n, fail, pi, best>>
     ELSE
        /\ pc' = "Done"
        /\ best' = MinOffset(str)
        /\ UNCHANGED <<fail, pi, i, str, n>>

\* stuttering after termination
DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, pi, i, best, pc>>

Next ==
  \/ Check
  \/ DoneStutter

vars == <<str, n, fail, pi, i, best, pc>>

Spec == Init /\ [][Next]_vars

\* type invariant
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n-1 -> (Undefined \cup 0..n-1)]
  /\ pi \in (Undefined \cup 0..n-1)
  /\ i \in Nat
  /\ i >= 1 /\ i <= 2*n
  /\ best \in 0..n-1
  /\ pc \in {"Check", "Done"}
  /\ CharSetSize \in Nat
  /\ CharacterSet = 0..CharSetSize

\* correctness: when finished, best yields the lexicographically minimal rotation
Correctness ==
  (pc = "Done") =>
    \A off \in 0..n-1 :
      LexLessOrEq(Rotate(str, best), Rotate(str, off))

====