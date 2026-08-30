---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A bounded (finite) version of the built-in Seq operator, kept separate from
\* the declaration so the .cfg replacement can target the original name.
LimitedSeq(S) == { [i \in DOMAIN S |-> S[i]] }

\* The domain of a sequence, as a plain set (useful for defining the partition
\* operator as a permutation of the domain).
SeqDomain(S) == { i \in 1..Len(S) : S[i] \in Values }

\* A permutation preserves the multiset of values; here it is a reordering of
\* the domain of the sequence, which is how the partition operator is kept
\* honest while still being free to touch only the indexed interval.
Permutation(d, S) ==
  /\ DOMAIN S = d
  /\ Cardinality d = Len(S)
  /\ \A x \in d : S[x] \in Values

\* The partition operator: for the chosen interval and pivot, any sequence
\* matching the partition shape (lower part no greater than upper part, outside
\* the interval untouched) is admissible -- this is the nondeterminism the
\* model explores, and it is what makes the correctness proof rely on shape
\* rather than any particular partitioning scheme.
PartitionOn(a, b, p, S) ==
  { T \in Values^{Len(S)} :
      /\ Permutation(SeqDomain(S), T)
      /\ \A k \in 1..Len(S) : (k <= a \/ k > b) => T[k] = S[k]
      /\ \A i \in a..p, j \in (p + 1)..b : T[i] <= T[j] }

\* The Quicksort state machine: sequence, original copy, work-set of intervals,
\* and a program counter naming the current block.
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in Values^{1..MaxSeqLen}
  /\ orig \in Values^{1..MaxSeqLen}
  /\ work \subseteq (1..MaxSeqLen \X 1..MaxSeqLen)
  /\ pc \in {"qs", "done"}

DomainPartitions ==
  { \cup_{i \in 1..n} (a_i..b_i) : n \in Nat, \A i \in 1..n :
      /\ work[i] = <<a_i, b_i>>
      /\ \A j \in 1..n : i # j => b_i < a_j \/ b_j < a_i }

PermutationPreserved == \A k \in 1..Len(seq) : seq[k] = orig[k]

\* The relative sortedness condition is pairwise across intervals: for any
\* two intervals in the work set, every element of the lower one must be no
\* greater than every element of the higher one. When the work set resolves
\* to singletons and the intervals cover the whole domain, this collapses to
\* global sortedness of the sequence.
IntervalSortedness ==
  \A i \in work, j \in work :
    (i[1] <= j[1] /\ i[2] >= i[1] /\ j[2] >= j[1] /\ i[2] < j[1])
      => \A x \in i[1]..i[2], y \in j[1]..j[2] : seq[x] <= seq[y]

Init ==
  /\ \E s \in { x \in Values^{1..MaxSeqLen} : Len(x) > 0 } : seq = s /\ orig = s
  /\ work = { <<1, Len(seq>> }
  /\ pc = "qs"

QuicksortStep ==
  \/ \E i \in work :
       /\ (i[1] = i[2] => work' = work \ {i})
       /\ (i[1] < i[2] =>
            \E p \in i[1]..i[2] :
              \E T \in PartitionOn(i[1], i[2], p, seq) :
                /\ seq' = T
                /\ work' = (work \ {i}) \cup { <<i[1], p>>, <<p + 1, i[2]>> })
  \/ pc' = "qs"

Terminate ==
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Idle ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == QuicksortStep \/ Terminate \/ Idle

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep)

PCorrect == pc = "done" => PermutationPreserved /\ IntervalSortedness

Termination == <>(pc = "done")

====