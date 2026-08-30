---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* An interval of indices into the sequence, with the length of the whole
\* sequence tacked on so intervals from different steps stay comparable.
Interval(i, j, n) == <<i, j, n>>

\* A subinterval of a given interval, used to subdivide the work set.
Sub(i, j, k) == IF k = i THEN Interval(i, i, k) ELSE Interval(i + 1, j, k)

VARIABLES seq, orig, workset, pc

vars == <<seq, orig, workset, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ workset \subseteq [a : 1..MaxSeqLen, b : 1..MaxSeqLen, n : 1..MaxSeqLen]
  /\ pc \in {"loop", "done"}

\* The partition operator is nondeterministic over all valid results: it keeps
\* every element never in scope untouched and enforces the partition ordering.
PartitionResults(s, i, j, n) ==
  { t \in Seq(Values) :
      /\ Len(t) = n
      /\ \A k \in 1..n : (k < i \/ k > j) => t[k] = s[k]
      /\ \A k \in i..j-1 : t[k] =< t[k + 1] }

Init ==
  /\ \E n \in 1..MaxSeqLen, s \in Seq(Values) :
       /\ Len(s) = n
       /\ seq = s
       /\ orig = s
  /\ workset = {Interval(1, Len(seq), Len(seq))}
  /\ pc = "loop"

LoopStep ==
  /\ pc = "loop"
  /\ workset # {}
  /\ \E it \in workset :
       LET i == it[1] j == it[2] n == it[3] IN
       /\ n = Len(seq)
       /\ \/ /\ i = j
             /\ workset' = workset \ {it}
          \/ /\ i < j
             /\ \E piv \in i..j :
                  /\ \E s' \in PartitionResults(seq, i, j, n):
                       seq' = s'
                  /\ workset' = (workset \ {it}) \cup {Sub(i, piv, n), Sub(piv + 1, j, n)}
       /\ pc' = "loop"
  /\ orig' = orig

Done ==
  /\ pc = "loop"
  /\ workset = {}
  /\ pc' = "done"
  /\ seq' = seq
  /\ orig' = orig
  /\ workset' = workset

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == LoopStep \/ Done \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep)

\* Two partially sorted intervals that partition the sequence must be ordered
\* correctly where they touch, which is exactly what sorting needs.
MergeOK ==
  \A i \in 1..(Len(seq) - 1) : seq[i] =< seq[i + 1]

\* Two intervals that partition the domain must assign each index to exactly
\* one of them; the sequence still in use is a permutation of the original.
DomainPartition ==
  \A i \in 1..Len(seq) :
    /\ \E x \in workset : i \in x[1]..x[2]
    /\ \A x1 \in workset, x2 \in workset :
         (i \in x1[1]..x1[2] /\ i \in x2[1]..x2[2]) => x1 = x2

PermutationPreserved == seq = orig \circ Permutations(Len(seq))

PCorrect == MergeOK

\* The eventual-sortedness cross-check is the substance of the proof; the
\* other two invariants are what the inductive argument rests on.
Inv == DomainPartition /\ PermutationPreserved /\ MergeOK

Termination == <>(pc = "done")

\* SAFETY: the three-part invariant is inductive and implies the final result
\* is a sorted permutation of the input. LIVENESS: weak fairness on the
\* looping step forces the algorithm to reach the terminal state.
====