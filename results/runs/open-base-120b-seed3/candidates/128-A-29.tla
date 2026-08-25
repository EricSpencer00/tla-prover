---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

Count(s, v) == 
  Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \A v \in Values : Count(s, v) = Count(t, v)

Sorted(s) ==
  \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

\* Intervals are represented as 2‑element sequences <<lo,hi>>
IsInterval(i, n) ==
  /\ Len(i) = 2
  /\ i[1] \in 1..n
  /\ i[2] \in i[1]..n

AllIntervals(n) == { i \in Seq(Nat) : IsInterval(i, n) }

\* Partition predicate: seq2 is a possible result of partitioning seq
\* over interval [lo,hi] with pivot p.
Partition(seq, seq2, lo, hi, p) ==
  /\ Len(seq2) = Len(seq)
  /\ \A j \in (1..Len(seq)) \ (lo..hi) : seq2[j] = seq[j]
  /\ \A j1 \in lo..p : \A j2 \in p+1..hi : seq2[j1] <= seq2[j2]
  /\ Permutation(seq, seq2)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Main loop when work is non‑empty
MainStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E i \in work :
       LET lo == i[1] IN
       LET hi == i[2] IN
       IF lo = hi THEN
         /\ work' = work \ {i}
         /\ UNCHANGED <<seq, orig, pc>>
       ELSE
         /\ \E p \in lo..hi :
              /\ \E seq2 \in LimitedSeq :
                    /\ Partition(seq, seq2, lo, hi, p)
                    /\ seq' = seq2
              /\ work' = (work \ {i})
                         \cup (IF lo <= p-1 THEN {<<lo, p-1>>} ELSE {})
                         \cup (IF p+1 <= hi THEN {<<p+1, hi>>} ELSE {})
              /\ orig' = orig
              /\ pc' = "Loop"
       END IF

\* 2. Termination step when work is empty
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

\* 3. Stuttering after termination
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == MainStep \/ Terminate \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ Len(seq) = Len(orig)
  /\ work \subseteq AllIntervals(Len(seq))
  /\ pc \in {"Loop", "Done"}

Inv == TypeOK /\ Permutation(seq, orig)

PCorrect == 
  pc = "Done" => Sorted(seq) /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

=============================================================================