---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen, Seq

\* Sequences of length zero are not reachable from the start, but the
\* type-legal space is included for completeness.
Sequences == UNION { [1..n -> Values] : n \in 1..MaxSeqLen }

VARIABLES seq, origSeq, todo, pc

vars == << seq, origSeq, todo, pc >>

Intervals == UNION { [1 .. n -> SUBSET (1 .. n)] : n \in 1..MaxSeqLen }

TypeOK ==
  /\ seq \in Sequences
  /\ origSeq \in Sequences
  /\ todo \in Intervals
  /\ pc \in {"run", "done"}

Init ==
  /\ seq \in Sequences
  /\ origSeq = seq
  /\ Cardinality(seq) >= 1
  /\ todo = {1 .. Cardinality(seq)}
  /\ pc = "run"

DomainPermutation(f) == (f \in [1 .. Cardinality(seq) -> 1 .. Cardinality(seq)])
                        /\ ( \A i, j \in 1 .. Cardinality(seq) : f[i] = f[j] => i = j )

PermutationOnDomain(b) ==
  \E f \in [1 .. Cardinality(seq) -> 1 .. Cardinality(seq)] :
    /\ DomainPermutation(f)
    /\ b = [i \in 1 .. Cardinality(seq) |-> seq[f[i]]]

\* An interval's partitioning may only re-order elements inside it, never move
\* elements across the pivot boundary.
ValidPartition(b, interval, pivot) ==
  /\ PermutationOnDomain(b)
  /\ \A i \in interval : i <= pivot => b[i] <= b[pivot]
  /\ \A i \in interval : i >= pivot => b[pivot] <= b[i]
  /\ \A i \in {1 .. Cardinality(seq)} \ interval : b[i] = seq[i]

PCorrect ==
  \/ (pc = "run")
  \/ (pc = "done" /\ \A i \in 1 .. Cardinality(seq) - 1 : seq[i] <= seq[i + 1])

SortedBetween(a, b) == \A i \in a, j \in b : i < j => seq[i] <= seq[j]

Inv ==
  /\ \A i \in todo : i <= Cardinality(seq)
  /\ \A i, j \in {1 .. Cardinality(seq)} : i \in todo /\ j \notin todo => i <= j => seq[i] <= seq[j]

\* A single iteration of the sorting loop, with the partition step abstracted
\* into an arbitrary-but-valid choice.
Loop ==
  /\ pc = "run"
  /\ \E interval \in todo :
       LET rest == todo \ {interval}
       IN IF Cardinality(interval) = 1
            THEN /\ todo' = rest
                 /\ UNCHANGED seq
            ELSE
              \E pivot \in interval :
                \E b \in Sequences :
                  /\ ValidPartition(b, interval, pivot)
                  /\ seq' = b
                  /\ todo' = rest \cup {1 .. pivot, pivot + 1 .. Cardinality(seq)}
  /\ UNCHANGED << origSeq, pc >>

Terminate ==
  /\ pc = "run"
  /\ todo = {}
  /\ pc' = "done"
  /\ UNCHANGED << seq, origSeq, todo >>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Loop \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

Permutation(b) ==
  \E f \in [1 .. Cardinality(seq) -> 1 .. Cardinality(seq)] :
    /\ DomainPermutation(f)
    /\ b = [i \in 1 .. Cardinality(seq) |-> origSeq[f[i]]]

Multiset(s) ==
  UNION { [v -> {i \in 1 .. Cardinality(s) : s[i] = v}] : v \in Values }

Sorted(s) == \A i \in 1 .. (Cardinality(s) - 1) : s[i] <= s[i + 1]

Termination ==
  /\ pc = "done"
  /\ Multiset(seq) = Multiset(origSeq)
  /\ Sorted(seq)

====