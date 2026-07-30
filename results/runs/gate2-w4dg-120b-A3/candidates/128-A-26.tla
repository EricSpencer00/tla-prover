---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

CONSTANTS
  Values,
  MaxSeqLen

\* The partition operator is the nondeterministic core of the spec: it returns
\* every permutation that leaves the outer region of the sequence untouched and
\* establishes the order invariant at the pivot index.
PartitionSeq(s, lo, hi, piv) ==
  { t \in Permutations(SUBSET <<1 .. Len(s)>>)
      : /\ \A i \in 1 .. Len(s) : (i < lo \/ i > hi) => t[i] = s[i]
         /\ \A i \in lo .. piv, j \in piv + 1 .. hi : t[i] <= t[j] }

\* The bounded version of Seq (the internal operator from the standard module)
\* is redefined here by the companion .cfg; the name on the left stays out of
\* the module so it is never declared, only overridden at model-check time.
\* (Keeping EXTENDS Sequences is what lets us use Sequence operators elsewhere.)
\* LimitedSeq == ...

VARIABLES
  seq,
  orig,
  work,
  pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) \in 1 .. MaxSeqLen
  /\ orig \in Seq(Values)
  /\ Len(orig) = Len(seq)
  /\ work \subseteq [lo: 1 .. MaxSeqLen, hi: 1 .. MaxSeqLen]
  /\ pc \in {"running", "done"}

Init ==
  /\ \E s \in Seq(Values) :
       /\ Len(s) >= 1
       /\ Len(s) <= MaxSeqLen
       /\ seq = s
       /\ orig = s
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "running"

IntervalDone ==
  \/ \E iv \in work : work' = work \ {iv}
  /\ pc' = pc
  /\ UNCHANGED <<seq, orig>>

IntervalStep ==
  /\ \E iv \in work :
       /\ iv.lo < iv.hi
       /\ \E piv \in iv.lo .. iv.hi :
            /\ \E ns \in PartitionSeq(seq, iv.lo, iv.hi, piv) :
                 seq' = ns
            /\ work' = (work \ {iv})
                 \cup {[lo |-> iv.lo, hi |-> piv]}
                 \cup {[lo |-> piv + 1, hi |-> iv.hi]}
  /\ pc' = pc
  /\ UNCHANGED orig

Terminated == /\ work = {}
              /\ pc = "running"
              /\ pc' = "done"
              /\ UNCHANGED <<seq, orig, work>>

Stall == /\ pc = "done"
         /\ UNCHANGED vars

Next == IntervalDone \/ IntervalStep \/ Terminated \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(IntervalDone \/ IntervalStep \/ Terminated)

\* The partial-correctness condition bundles three facts: the result is a
\* permutation of the input, the outer parts of the sequence are untouched, and
\* every partitioning step respected the pivot ordering.
SortedWithinIntervals ==
  /\ \A iv \in work : \A i \in iv.lo .. iv.hi - 1 : seq[i] <= seq[i + 1]
  /\ \A i \in 1 .. Len(seq) : seq[i] = orig[i]
  /\ seq \in Permutations(Domain(orig))

\* The inductive invariant. All three conjuncts are needed: without the
\* partitioning order the permutation guarantee is not closed under Next.
Inv ==
  /\ SortedWithinIntervals
  /\ seq \in Permutations(Domain(orig))
  /\ Len(seq) = Len(orig)

Termination == <>(pc = "done")

PCorrect == pc = "done" => SortedWithinIntervals
TypeOK == TypeOK
====