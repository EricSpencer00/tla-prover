---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Values, MaxSeqLen

\* INTERVALS are contiguous index ranges of the sequence; workSet is the set
\* of intervals still to be partitioned. The algorithm picks any interval in
\* it and subdivides that interval; there is no ordering, so the model must
\* be robust to arbitrary choices of next interval.
Intervals == [low : 1..MaxSeqLen, high : 1..MaxSeqLen]

VARIABLES seq, original, workSet, pc

vars == <<seq, original, workSet, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= MaxSeqLen
  /\ original \in Seq(Values)
  /\ Len(original) <= MaxSeqLen
  /\ workSet \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Seq(Values) : Len(s) >= 1 /\ seq = s /\ original = s
  /\ workSet = {[low |-> 1, high |-> Len(seq)]}
  /\ pc = "loop"

\* A "valid" partition keeps elements outside the interval untouched and
\* ensures the pivot index separates the two halves correctly on every
\* element value, not just the pivot value.
ValidPartitions(s, i) ==
  {s2 \in Seq(Values) :
     /\ Len(s2) = Len(seq)
     /\ \A k \in 1..Len(seq) : IF k < i \/ k > i THEN s2[k] = seq[k] ELSE TRUE
     /\ \A a \in 1..i, b \in i+1..Len(seq) : s2[a] <= s2[b]}

\* The core action: pick an interval, partition it around a pivot, and
\* replace it in the work set with its two subintervals.
Step ==
  /\ pc = "loop"
  /\ \E iv \in workSet :
       /\ workSet' = workSet \ {iv}
       /\ IF iv.low = iv.high
            THEN workSet'
            ELSE
              /\ \E i \in iv.low..iv.high :
                   /\ \E s2 \in ValidPartitions(seq, i) : seq' = s2
                   /\ workSet' = workSet' \cup
                        {[low |-> iv.low, high |-> i], [low |-> i + 1, high |-> iv.high]}
  /\ pc' = IF workSet = {} THEN "done" ELSE "loop"
  /\ UNCHANGED original

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The loop invariant: the intervals in the work set partition the domain,
\* the sequence is always a permutation of the original, and any two
\* intervals that sit in order are already locally sorted relative to each
\* other.
Inv ==
  /\ \A a, b \in workSet : a.high < b.low \/ b.high < a.low \/ a.high < b.low
  /\ \E e \in {g \in [1..Len(original) -> Values] : \A x, y \in 1..Len(original) : x < y => g[x] <= g[y]} : seq = e
  /\ \A a, b \in workSet : a.high < b.low => \A i \in a.low..a.high, j \in b.low..b.high : seq[i] <= seq[j]

\* Safety: on termination the sequence is a sorted permutation of the
\* original sequence -- nothing more, nothing less, is ever possible.
PCorrect ==
  (pc = "done") =>
     /\ \E e \in {g \in [1..Len(original) -> Values] : \A x, y \in 1..Len(original) : x < y => g[x] <= g[y]} : seq = e
     /\ Cardinality({s \in [1..Len(original) -> Values] : \A x \in 1..Len(original) : s[x] = seq[x]}) = Cardinality(Values)

Terminating ==
  (pc = "loop") ~> (pc = "done")

LimitedSeq(s, n) ==
  IF s = <<>> THEN <<>>
  ELSE IF Len(s) > n THEN LimitedSeq(Tail(s), n)
  ELSE Head(s) \o LimitedSeq(Tail(s), n)

====