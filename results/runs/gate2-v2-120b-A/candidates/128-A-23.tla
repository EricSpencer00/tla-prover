---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Indices == 1 .. MaxSeqLen

\* An interval is a contiguous range of indices, represented as a record
INTERVAL == [lo : Nat, hi : Nat]
IsInterval(i) == i.lo <= i.hi /\ i.lo \in Indices /\ i.hi \in Indices

\* The set of all possible intervals over the current length of the sequence
AllIntervals(len) == { [lo |-> a, hi |-> b] :
                        a \in 1..len,
                        b \in a..len }

\* The work set is a set of intervals that still need to be processed
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* State predicates
\* ----------------------------------------------------------------------
\* seq is the current sequence (length may be < MaxSeqLen but we treat the
\* tail as uninterpreted)
SeqOK == /\ \A i \in Indices: IF i <= Len(seq) THEN seq[i] \in Values ELSE TRUE
\* orig is a copy of the initial sequence
OrigOK == /\ \A i \in Indices: IF i <= Len(orig) THEN orig[i] \in Values ELSE TRUE

\* work is a set of intervals, each interval lies within the current length
WorkOK == /\ \A i \in work: IsInterval(i)
          /\ \A i \in work: i.lo <= Len(seq) /\ i.hi <= Len(seq)

TypeOK == /\ SeqOK /\ OrigOK /\ WorkOK /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
/\ Len(seq) = MaxSeqLen
/\ seq = [i \in Indices |-> CHOOSE v \in Values : TRUE] \* nondet full-length seq
/\ orig = seq
/\ work = { [lo |-> 1, hi |-> MaxSeqLen] }
 /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Partition operation (abstract)
\* Given an interval i and a pivot index p, returns a set of possible
\* sequences that satisfy the partition contract.
\* We model it nondeterministically via an existential quantifier.
\* ----------------------------------------------------------------------
Partition(i, p, oldSeq) ==
  { newSeq \in Seq :
      /\ Len(newSeq) = Len(oldSeq)
      /\ \A j \in Indices:
           IF j \notin i.lo .. i.hi
           THEN newSeq[j] = oldSeq[j]
           ELSE IF j <= p
                THEN newSeq[j] <= newSeq[p]
                ELSE newSeq[j] >= newSeq[p] }

\* ----------------------------------------------------------------------
\* Main transition
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E i \in work:
        /\ IsInterval(i)
        /\ IF i.lo = i.hi
           THEN /\ work' = work \ {i}
                /\ UNCHANGED <<seq, orig>>
           ELSE /\ \E p \in i.lo .. i.hi:
                 /\ \E newSeq \in Partition(i, p, seq):
                       /\ seq' = newSeq
                       /\ work' = (work \ {i}) \cup
                                 { [lo |-> i.lo, hi |-> p],
                                   [lo |-> p+1, hi |-> i.hi] }
                       /\ UNCHANGED orig
        /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Safety invariant: partial correctness
\* When the algorithm has terminated (pc = "Done"), the sequence is a
\* permutation of the original and is sorted.
\* ----------------------------------------------------------------------
Sorted(s) ==
  \A i, j \in Indices :
    (i < j /\ i <= Len(s) /\ j <= Len(s)) => s[i] <= s[j]

Permutation(s, t) ==
  \A v \in Values : 
    \A i \in Indices :
      (i <= Len(s) /\ i <= Len(t)) => 
        (s[i] = v) <=> ( \E j \in Indices : j <= Len(t) /\ t[j] = v)

PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* General invariant (used for type checking and to help the model checker)
\* ----------------------------------------------------------------------
Inv == /\ TypeOK
      /\ PCorrect

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Theorems (optional, just to expose the invariant)
\* ----------------------------------------------------------------------
THEOREM InvIsInvariant == Spec => []Inv

====