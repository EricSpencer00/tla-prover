---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LimitedSeq(Val, max) ==
  { s \in Seq(Val) : Len(s) <= max /\ Len(s) >= 1 }

\* An interval is a pair <<lo,hi>> with 1 <= lo <= hi <= Len(seq)
INTERVAL(seq) ==
  { <<lo,hi>> : lo \in 1..Len(seq), hi \in lo..Len(seq) }

\* Returns the two (non‑empty) sub‑intervals obtained by splitting [i..j] at pivot p
SubIntervals(i, j, p) ==
  (IF i <= p-1 THEN { <<i, p-1>> } ELSE {}) \cup
  (IF p+1 <= j THEN { <<p+1, j>> } ELSE {})

\* Predicate stating that s2 is a permutation of s1 (full sequences)
Permutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \E f \in [1..Len(s1) -> 1..Len(s1)] :
        /\ \A i \in 1..Len(s1) : f[i] \in 1..Len(s1)
        /\ \A i, j \in 1..Len(s1) : (f[i] = f[j]) => i = j   \* f is bijective
        /\ \A i \in 1..Len(s1) : s2[i] = s1[f[i]]

\* Predicate that the sequence is sorted in non‑decreasing order
Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Predicate specifying a valid partition result for interval [i..j] with pivot p
PartitionResult(old, new, i, j, p) ==
  /\ i <= p /\ p < j
  /\ \A idx \in 1..Len(old) :
        (idx < i \/ idx > j) => new[idx] = old[idx]   \* outside interval unchanged
  /\ \A a \in i..p :
        \A b \in p+1..j :
            new[a] <= new[b]                         \* lower part ≤ upper part
  /\ Permutation(<<old[i..j]>>, <<new[i..j]>>)       \* multiset of the interval preserved

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Choose an interval to process
PickInterval ==
  /\ pc = "Run"
  /\ work # {}
  /\ \E I \in work :
        LET lo == I[1] IN hi == I[2] IN
        IF lo = hi THEN
          /\ work' = work \ {I}
          /\ seq' = seq
          /\ orig' = orig
          /\ pc' = "Run"
        ELSE
          /\ \E p \in lo..hi :
                LET lower  == SubIntervals(lo, hi, p) IN
                /\ newSeq \in LimitedSeq(Values, MaxSeqLen)
                /\ PartitionResult(seq, newSeq, lo, hi, p)
                /\ seq' = newSeq
                /\ work' = (work \ {I}) \cup lower
                /\ orig' = orig
                /\ pc' = "Run"
        \* end IF
  /\ UNCHANGED <<orig>>

\* Termination step
Terminate ==
  /\ pc = "Run"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

\* Stuttering after termination
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ PickInterval
  \/ Terminate
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig \in LimitedSeq(Values, MaxSeqLen)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq INTERVAL(seq)
  /\ pc \in {"Run", "Done"}

Inv ==
  /\ TypeOK
  /\ (pc = "Done" => Sorted(seq) /\ Permutation(orig, seq))

PCorrect ==
  /\ pc = "Done"
  => Sorted(seq) /\ Permutation(orig, seq)

\* ----------------------------------------------------------------------
\* Property (liveness)
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect

====