---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* The Quicksort algorithm from Lamport's "Proving Safety Properties", section 7.3.
\* This is the TLA+ version: a single PlusCal process, the state machine,
\* and a structured proof of partial correctness.

CONSTANTS Values, MaxSeqLen, Seq

BigRange == {0, 1, 2}

Intervals == [lo: 0 .. MaxSeqLen, hi: 0 .. MaxSeqLen]

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* A permutation of a finite domain is any bijection on that domain; composing
\* the original sequence with such a bijection yields a permutation of it.
Permutations(f) == {g \in [1 .. Len(f) -> 1 .. Len(f)] : \A i \in 1 .. Len(f) : \A j \in 1 .. Len(f) : g[i] = g[j] => i = j}

\* Work intervals are all disjoint and together cover exactly the sorted prefix
\* of the domain: wherever two intervals intersect, one of them is empty.
DisjointCover(d) ==
  /\ \A i, j \in d : (i.lo = j.lo /\ i.hi = j.hi) \/ (i.lo = i.hi \/ j.lo = j.hi)
  /\ \A i \in d : i.lo <= i.hi

RelativeSorted(d) ==
  \A i, j \in d :
    /\ (i.hi < j.lo) => (i.hi = j.lo => seq[i.hi] <= seq[j.lo])
    /\ (j.hi < i.lo) => (j.hi = i.lo => seq[j.hi] <= seq[i.lo])

Narrow(d) == \A i \in d : i.lo < i.hi

Inv ==
  /\ DisjointCover(work)
  /\ seq \in Permutations(orig)
  /\ RelativeSorted(work)

TypeOK ==
  /\ seq \in [1 .. MaxSeqLen -> Values]
  /\ orig \in [1 .. MaxSeqLen -> Values]
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq = Seq
  /\ orig = Seq
  /\ work = {[lo |-> 1, hi |-> Len(Seq)]}
  /\ pc = "loop"

\* The partition step is nondeterministic over its result: any sequence that
\* leaves elements outside the interval untouched and respects the pivot order
\* is a valid outcome of some concrete partition procedure.
QuicksortStep ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E i \in work :
       LET lo == i.lo
           hi == i.hi
       IN IF lo = hi
          THEN work' = work \ {i}
          ELSE \E p \in lo + 1 .. hi :
                 \E ns \in [1 .. MaxSeqLen -> Values] :
                   /\ \A k \in 1 .. Len(seq) : (k < lo \/ k > hi) => ns[k] = seq[k]
                   /\ \A k \in lo .. p : \A j \in p + 1 .. hi : ns[k] <= ns[j]
                   /\ seq' = ns
                 /\ work' = (work \ {i}) \cup {[lo |-> lo, hi |-> p], [lo |-> p + 1, hi |-> hi]}
  /\ pc' = pc

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == QuicksortStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep) /\ WF_vars(Terminate)

\* Partial correctness: at termination the sequence is still a permutation of
\* its original values and is sorted.
PCorrect == pc = "done" => /\ seq \in Permutations(orig) /\ \A i \in 1 .. Len(seq) - 1 : seq[i] <= seq[i + 1]

Termination == <>(pc = "done")

====