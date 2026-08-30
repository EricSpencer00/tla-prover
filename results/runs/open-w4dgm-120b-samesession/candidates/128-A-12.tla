---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* Intervals are half-open ranges of positions in the sequence.
Interval == [lo: 1 .. MaxSeqLen, hi: 1 .. MaxSeqLen]
Domain == 1 .. MaxSeqLen

\* Permutations of the domain are composable and invertible, and compose
\* pointwise with the sequence values to express permutation invariants.
Permutation == [Domain -> Domain]
IdPerm == [i \in Domain |-> i]
Compose(p, q) == [i \in Domain |-> p[q[i]]]
Apply(f, seq) == [i \in Domain |-> seq[f[i]]]

\* A partitioning only permutes values within the chosen interval and
\* leaves values below the pivot no greater than those above it.
Partitioning(seq, ints, p, i) ==
  { Apply(f, seq) :
      \E f \in Permutation :
        /\ \A j \in Domain : (j < ints[i].lo \/ j >= ints[i].hi) => f[j] = j
        /\ \A j \in ints[i].lo .. i : seq[j] <= seq[i]
        /\ \A j \in i + 1 .. ints[i].hi - 1 : seq[j] >= seq[i] }

VARIABLES seq, orig, pending, pc

vars == <<seq, orig, pending, pc>>

TypeOK ==
  /\ seq \in [Domain -> Values]
  /\ orig \in [Domain -> Values]
  /\ pending \subseteq Interval
  /\ pc \in {"loop", "done"}

Init ==
  \E s \in Seq(Values) :
    /\ s # <<>>
    /\ Len(s) <= MaxSeqLen
    /\ seq = [i \in Domain |-> s[i]]
    /\ orig = [i \in Domain |-> s[i]]
    /\ pending = {[lo |-> 1, hi |-> Len(s)]}
    /\ pc = "loop"

PCorrect ==
  (\A i, j \in Domain : seq[i] = seq[j] <=> orig[i] = orig[j]) /\ Len(seq) = Len(orig)

\* A domain partition is maintained by the interval set and the sequence.
DomainPartition ==
  /\ (pending = {} <=> Len(seq) = 0)
  /\ pending \subseteq {i \in Interval : i.hi <= Len(seq) + 1}
  /\ \A i \in pending : i.lo < i.hi
  /\ \A a, b \in pending : a # b => (a.hi <= b.lo \/ b.hi <= a.lo)

RelativeSorted ==
  \A a, b \in pending : (a.hi = b.lo) => seq[a.hi - 1] <= seq[b.lo]

Inv == PCorrect /\ DomainPartition /\ RelativeSorted

Step ==
  IF pc = "loop" THEN
    IF pending = {} THEN
      pc' = "done"
    ELSE
      \E i \in pending :
        /\ pending' = pending \ {i}
        /\ IF i.hi - i.lo = 1 THEN UNCHANGED seq
           ELSE
             \E p \in 1 .. Len(seq), s \in Partitioning(seq, pending, p, i.lo) :
               /\ seq' = s
               /\ pending' = pending \cup {[lo |-> i.lo, hi |-> p + 1], [lo |-> p + 2, hi |-> i.hi]}
        /\ UNCHANGED <<orig, pc>>
  ELSE UNCHANGED vars

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Termination == <>(pc = "done")

\* LimitedSeq makes the model finite without sacrificing the algorithm.
LimitedSeq == Seq

====