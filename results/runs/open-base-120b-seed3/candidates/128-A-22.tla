---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Count(seq, val, l, h) ==
  Cardinality({ k \in l..h : seq[k] = val })

IsPermutation(seq1, seq2, l, h) ==
  /\ Len(seq1) = Len(seq2)
  /\ \A v \in Values : Count(seq1, v, l, h) = Count(seq2, v, l, h)

Sorted(seq) ==
  \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

\* Interval is a record with fields l (left) and h (right)
Interval == [l : Nat, h : Nat]

IsValidInterval(i, n) ==
  /\ i.l \in 1..n
  /\ i.h \in 1..n
  /\ i.l <= i.h

PartitionSet(seq, l, h, p) ==
  { seq2 \in LimitedSeq(Values) :
      /\ Len(seq2) = Len(seq)
      /\ \A k \in 1..Len(seq) :
            (k < l \/ k > h) => seq2[k] = seq[k]
      /\ \A i \in l..p : \A j \in p+1..h :
            seq2[i] <= seq2[j]
      /\ IsPermutation(seq, seq2, l, h) }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [l |-> 1, h |-> Len(seq)] }
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Main action (one loop iteration)
\* ----------------------------------------------------------------------
MainAction ==
  /\ pc = "Run"
  /\ work # {}
  /\ \E i \in work :
        LET l == i.l
            h == i.h
        IN
          IF l = h THEN
            /\ seq' = seq
            /\ orig' = orig
            /\ work' = work \ { i }
            /\ pc' = pc
          ELSE
            /\ \E p \in l..h :
                 /\ seq' \in PartitionSet(seq, l, h, p)
                 /\ orig' = orig
                 /\ pc' = pc
                 /\ work' = (work \ { i })
                           \cup (IF l <= p-1 THEN { [l |-> l, h |-> p-1] } ELSE {})
                           \cup (IF p+1 <= h THEN { [l |-> p+1, h |-> h] } ELSE {})
         

\* ----------------------------------------------------------------------
\* Termination action
\* ----------------------------------------------------------------------
Terminate ==
  /\ pc = "Run"
  /\ work = {}
  /\ seq' = seq
  /\ orig' = orig
  /\ work' = work
  /\ pc' = "Done"

\* ----------------------------------------------------------------------
\* Stuttering step after termination (to avoid deadlock)
\* ----------------------------------------------------------------------
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED << seq, orig, work, pc >>

Next ==
  \/ MainAction
  \/ Terminate
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq { i \in Interval : IsValidInterval(i, Len(seq)) }
  /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Global permutation invariant
\* ----------------------------------------------------------------------
Inv ==
  /\ TypeOK
  /\ IsPermutation(seq, orig, 1, Len(seq))

\* ----------------------------------------------------------------------
\* Partial correctness when terminated
\* ----------------------------------------------------------------------
PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, orig, 1, Len(seq)))

\* ----------------------------------------------------------------------
\* Liveness: eventual termination
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

====