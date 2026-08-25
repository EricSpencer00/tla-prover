---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* ------------------------------------------------------------
\* Bounded version of Seq(S) used by the model checker
\* ------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ------------------------------------------------------------
\* Interval type (contiguous range of indices)
\* ------------------------------------------------------------
Interval == [lo : Nat, hi : Nat]

\* ------------------------------------------------------------
\* Convenience definitions
\* ------------------------------------------------------------
INTERVALS == { i \in Interval :
                i.lo <= i.hi /\ 1 <= i.lo /\ i.hi <= Len(seq) }

Count(seq, lo, hi, v) ==
  Cardinality({ j \in lo..hi : seq[j] = v })

IsPermutation(seq1, seq2) ==
  /\ Len(seq1) = Len(seq2)
  /\ \A v \in Values : Count(seq1, 1, Len(seq1), v) = Count(seq2, 1, Len(seq2), v)

Sorted(seq) ==
  \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

\* ------------------------------------------------------------
\* Variables
\* ------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ------------------------------------------------------------
\* Initial state
\* ------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Loop"

\* ------------------------------------------------------------
\* Action: remove a singleton interval
\* ------------------------------------------------------------
RemoveSingleton ==
  /\ pc = "Loop"
  /\ \E i \in work :
        /\ i.lo = i.hi
        /\ work' = work \ {i}
        /\ UNCHANGED <<seq, orig, pc>>

\* ------------------------------------------------------------
\* Action: partition a non‑singleton interval
\* ------------------------------------------------------------
PartitionStep ==
  /\ pc = "Loop"
  /\ \E i \in work :
        /\ i.lo < i.hi
        /\ \E p \in i.lo .. i.hi :
              /\ \E s2 \in LimitedSeq(Values) :
                    /\ Len(s2) = Len(seq)
                    /\ \A j \in 1..Len(seq) :
                         IF j < i.lo \/ j > i.hi THEN s2[j] = seq[j] ELSE TRUE
                    /\ \A j \in i.lo .. p :
                         \A k \in p+1 .. i.hi :
                              s2[j] <= s2[k]
                    /\ (\A v \in Values :
                         Count(seq, i.lo, i.hi, v) = Count(s2, i.lo, i.hi, v))
                    /\ seq' = s2
                    /\ work' =
                         (work \ {i}) \cup
                         (IF i.lo <= p THEN { [lo |-> i.lo, hi |-> p] } ELSE {}) \cup
                         (IF p+1 <= i.hi THEN { [lo |-> p+1, hi |-> i.hi] } ELSE {})
                    /\ UNCHANGED orig
                    /\ pc' = "Loop"

\* ------------------------------------------------------------
\* Action: terminate when work set is empty
\* ------------------------------------------------------------
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

\* ------------------------------------------------------------
\* Stuttering step after termination (prevents deadlock)
\* ------------------------------------------------------------
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

\* ------------------------------------------------------------
\* Next-state relation
\* ------------------------------------------------------------
Next == \/ RemoveSingleton
        \/ PartitionStep
        \/ Terminate
        \/ Stutter

\* ------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------
Spec == Init /\ [][Next]_<|seq, orig, work, pc|>

\* ------------------------------------------------------------
\* Type correctness invariant
\* ------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq INTERVALS
  /\ pc \in {"Loop", "Done"}

\* ------------------------------------------------------------
\* Main inductive invariant (permutation preservation)
\* ------------------------------------------------------------
Inv ==
  /\ TypeOK
  /\ IsPermutation(seq, orig)

\* ------------------------------------------------------------
\* Partial‑correctness property (holds when algorithm terminates)
\* ------------------------------------------------------------
PCorrect ==
  pc = "Done" => /\ IsPermutation(seq, orig)
                 /\ Sorted(seq)

\* ------------------------------------------------------------
\* Liveness property: eventual termination
\* ------------------------------------------------------------
Termination == <> (pc = "Done")

=============================================================================