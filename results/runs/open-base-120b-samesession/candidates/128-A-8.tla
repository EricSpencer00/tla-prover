---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Bounded sequence operator (replaces Seq from Sequences)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Helper definitions
Count(v, s) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(old, new) ==
  /\ Len(old) = Len(new)
  /\ \A v \in Values : Count(v, old) = Count(v, new)

Permutations(seq) == { s \in LimitedSeq(Values) : Permutation(seq, s) }

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Partition operator: all sequences that are permutations of the old one,
\* keep elements outside the interval unchanged, and satisfy the
\* ordering condition with respect to the pivot.
Partition(old, lo, hi, p) ==
  { new \in Permutations(old) :
      /\ \A i \in 1..Len(old) :
           (i < lo \/ i > hi) => new[i] = old[i]
      /\ \A i \in lo..p :
           \A j \in p+1..hi :
               new[i] <= new[j] }

\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* Tuple of all variables for the stuttering operator
vars == <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ seq \in LimitedSeq(Values)       \* non‑empty sequence
  /\ seq # <<>>                       \* ensure non‑empty
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }       \* single interval covering whole seq
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Main sorting step
MainAction ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E I \in work :
        LET lo == I[1] IN
        LET hi == I[2] IN
        /\ IF lo = hi THEN
              /\ seq' = seq
              /\ work' = work \ {I}
           ELSE
              /\ \E p \in lo..hi :
                     /\ let newSeq == CHOOSE s \in Partition(seq, lo, hi, p) : TRUE
                     IN
                     /\ seq' = newSeq
                     /\ work' = (work \ {I})
                                   \cup
                                   (IF lo <= p-1 THEN {<<lo, p-1>>} ELSE {})
                                   \cup
                                   (IF p+1 <= hi THEN {<<p+1, hi>>} ELSE {})
        /\ pc' = "Loop"

\* ----------------------------------------------------------------------
\* Termination step
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

\* ----------------------------------------------------------------------
\* Stuttering after termination (prevents deadlock)
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == \/ MainAction \/ Terminate \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ \A I \in work :
        LET lo == I[1] IN LET hi == I[2] IN
        /\ 1 <= lo /\ lo <= hi /\ hi <= Len(seq)
  /\ pc \in {"Loop", "Done"}

Inv == /\ TypeOK
       /\ Permutation(orig, seq)

PCorrect ==
  /\ pc = "Done"
  => /\ Sorted(seq)
     /\ Permutation(orig, seq)

\* ----------------------------------------------------------------------
\* Liveness property (termination)
Termination == <> (pc = "Done")

=============================================================================