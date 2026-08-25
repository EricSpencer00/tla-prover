---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq for model checking
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
IntervalLow(I) == I[1]
IntervalHigh(I) == I[2]

AllIntervals == { I \in Seq(Nat) :
                    /\ Len(I) = 2
                    /\ I[1] \in Nat
                    /\ I[2] \in Nat
                    /\ I[1] <= I[2]
                    /\ I[1] >= 1
                    /\ I[2] <= Len(seq) }

Count(seq_, lo, hi, v) ==
  Cardinality({ i \in lo..hi : seq_[i] = v })

PermutationPreserved(seq_, orig_) ==
  \A v \in Values : Count(seq_, 1, Len(seq_), v) = Count(orig_, 1, Len(orig_), v)

IsSorted(seq_) ==
  \A i, j \in 1..Len(seq_) : i < j => seq_[i] <= seq_[j]

PartitionPredicate(seq_, seq2_, lo, hi, p) ==
  /\ Len(seq2_) = Len(seq_)
  /\ \A i \in 1..Len(seq_) : (i < lo \/ i > hi) => seq2_[i] = seq_[i]
  /\ \A i \in lo..hi : seq2_[i] \in Values
  /\ \A v \in Values :
        Count(seq_, lo, hi, v) = Count(seq2_, lo, hi, v)
  /\ \A i \in lo..p   : seq2_[i] <= seq2_[p]
  /\ \A i \in p+1..hi : seq2_[i] >= seq2_[p]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ \E s \in LimitedSeq(Values) :
        /\ Len(s) > 0
        /\ seq = s
        /\ orig = s
        /\ work = { <<1, Len(s)>> }
        /\ pc   = "Loop"

\* ----------------------------------------------------------------------
\* Main transition
LoopAction ==
  /\ pc = "Loop"
  /\ IF work = {}
     THEN /\ pc' = "Done"
          /\ UNCHANGED <<seq, orig, work>>
     ELSE
        \E I \in work :
          LET lo == IntervalLow(I) IN
          LET hi == IntervalHigh(I) IN
          IF lo = hi
          THEN /\ work' = work \ {I}
               /\ pc'   = "Loop"
               /\ UNCHANGED <<seq, orig>>
          ELSE
            \E p \in lo..hi :
              LET lower == IF lo <= p-1 THEN { <<lo, p-1>> } ELSE {} IN
              LET upper == IF p+1 <= hi THEN { <<p+1, hi>> } ELSE {} IN
                \E s2 \in LimitedSeq(Values) :
                  /\ PartitionPredicate(seq, s2, lo, hi, p)
                  /\ seq' = s2
                  /\ work' = (work \ {I}) \cup lower \cup upper
                  /\ pc'   = "Loop"
                  /\ UNCHANGED orig

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  LoopAction \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
vars == <<seq, orig, work, pc>>
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ pc \in {"Loop", "Done"}
  /\ work \subseteq AllIntervals

\* ----------------------------------------------------------------------
\* General invariant (permutation preservation)
Inv ==
  TypeOK /\ PermutationPreserved(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness when terminated
PCorrect ==
  (pc = "Done") => (IsSorted(seq) /\ PermutationPreserved(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
Termination ==
  <> (pc = "Done")

=============================================================================