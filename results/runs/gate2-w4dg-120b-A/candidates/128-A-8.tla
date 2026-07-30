---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Integers

\* One-action Quicksort: the partition step is nondeterministic over every
\* result a real partitioning could produce, rather than a concrete procedure.
\* The invariants are the partition-of-domains relation, the permutation
\* relation, and the relative order of the two produced intervals.
\* The Spec name, the Init and Next actions, the PCorrect, TypeOK, Inv
\* invariants, and the Termination property are all required by the cfg file.

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

MaxSeq == Len(Seq)

\* Intervals are addressed by index; subintervals are simply the lower and
\* upper halves around a pivot index, which is the whole point of the model.
Interval == [lo: 1..MaxSeq, hi: 1..MaxSeq]

Low(i, iv) == iv.lo <= i /\ i <= iv.hi

InRange(i, iv) == iv.lo <= i /\ i <= iv.hi

\* Intervals partition the domain: two intervals share a position only when
\* the pivot index is in the middle and both sides belong to the same range.
\* This is exactly what keeps the work set tree-shaped rather than overlapping.
Partitioned(S) ==
  /\ \A a, b \in S : \A i \in 1..MaxSeq :
       (InRange(i, a) /\ InRange(i, b)) => (a.lo = b.lo /\ a.hi = b.hi)
  /\ \A a \in S : a.lo <= a.hi

\* Permutations are through automorphisms: a reordering that simply moves
\* elements between the two sides of the chosen pivot interval.
Automorphic(f, iv) ==
  /\ DOMAIN f = 1..MaxSeq
  /\ \A i \in 1..MaxSeq : f[i] >= iv.lo /\ f[i] <= iv.hi \/ ~Low(i, iv)
  /\ \A i \in 1..MaxSeq : ~Low(i, iv) => f[i] = i
  /\ \A i, j \in 1..MaxSeq :
       (f[i] > iv.hi /\ f[j] <= iv.hi) => seq[f[i]] >= seq[f[j]]

\* A permutation of seq that puts the two sides of a pivot in order.
Partitions(iv, s) ==
  \E f \in [1..MaxSeq -> 1..MaxSeq] :
    /\ Automorphic(f, iv)
    /\ s = [i \in 1..MaxSeq |-> seq[f[i]]]

\* The upper side of a split can never be smaller than the lower side at the
\* pivot index, which is what makes the whole structure sortable.
MiddleOrdered(iv) ==
  \A i \in 1..MaxSeq, j \in 1..MaxSeq :
    /\ InRange(i, iv) /\ i <= iv.hi
    /\ InRange(j, iv) /\ j > iv.hi
    => seq[i] <= seq[j]

TypeOK ==
  /\ seq \in Seq(Vals)
  /\ original \in Seq(Vals)
  /\ work \in SUBSET Interval
  /\ pc \in {"loop", "done"}

PCorrect ==
  (pc = "done") => (\A i \in 1..MaxSeq : seq[i] >= seq[i-1])

Inv ==
  /\ Partitioned(work)
  /\ \A i \in 1..MaxSeq : \E j \in 1..MaxSeq : seq[i] = original[j]
  /\ \A iv \in work : MiddleOrdered(iv)

Init ==
  /\ seq = Seq
  /\ original = Seq
  /\ work = {[lo |-> 1, hi |-> MaxSeq]}
  /\ pc = "loop"

Next ==
  \/ \E iv \in work :
       \/ IF iv.lo = iv.hi
          THEN /\ work' = work \ {iv}
               /\ UNCHANGED <<seq, original>>
          ELSE
            /\ \E s \in Vals :
                 /\ s = Seq
                 /\ Partitions(iv, s)
                 /\ seq' = s
                 /\ work' = (work \ {iv}) \cup {[lo |-> iv.lo, hi |-> iv.hi], [lo |-> iv.hi + 1, hi |-> iv.hi]}
                 /\ UNCHANGED original
    /\ pc' = "loop"
  \/ (pc = "loop" /\ work = {}) /\ pc' = "done"
  \/ (pc = "done") /\ UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

Termination == <>(pc = "done")

====