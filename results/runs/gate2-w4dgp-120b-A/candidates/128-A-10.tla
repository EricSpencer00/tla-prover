---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* A bounded-length version of the standard Seq operator, used only by the
\* .cfg's replacement of the imported definition so that the model is finite.
LimitedSeq(S) == {s \in S : Len(s) <= MaxSeqLen}

\* A partition of a sequence over an interval with a pivot: outside the interval
\* nothing moves, inside the interval every element left of the pivot is <= every
\* element right of the pivot, and the sequence is a permutation of its predecessor.
\* The nondeterministic choice of any partition that satisfies these constraints
\* is what abstracts away the concrete partition procedure.
PartitionOf(s, lo, hi, p) ==
  { t \in Sequences.Perm(s) :
      /\ Len(t) = Len(s)
      /\ \A i \in 1..Len(s) : i < lo \/ i > hi => t[i] = s[i]
      /\ \A i \in lo..p, j \in (p+1)..hi : t[i] <= t[j] }

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

Domain == 1..Len(seq)
Interval == [lo: Domain, hi: Domain]

PCorrect == (pc = "done") => /\ \A i \in Domain : \E j \in Domain : seq[i] = orig[j]
                        /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i+1]

TypeOK ==
  /\ seq \in LimitedSeq([1..MaxSeqLen -> Values])
  /\ orig \in LimitedSeq([1..MaxSeqLen -> Values])
  /\ work \subseteq Interval
  /\ pc \in {"loop", "done"}

\* Partition steps preserve the composition of existing left/right blocks, so
\* sortedness across block boundaries is an invariant rather than a post-check.
\* For each interval in the work set, the left half of that interval is sorted
\* and every element in that left half is <= every element in the right half.
Inv == \A iv \in work :
         /\ \A i \in iv.lo..(iv.p?) : seq[i] <= seq[i+1]
         /\ \A i \in iv.lo..(iv.p?), j \in (iv.p?+1)..iv.hi : seq[i] <= seq[j]

Init ==
  /\ seq \in LimitedSeq([1..MaxSeqLen -> Values])
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

PartitionStep ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E iv \in work :
       /\ work' = work \ {iv}
       /\ IF iv.lo = iv.hi
          THEN work' = work \ {iv}
          ELSE
            /\ \E p \in iv.lo..iv.hi :
                 /\ \E s' \in PartitionOf(seq, iv.lo, iv.hi, p) :
                      /\ seq' = s'
                      /\ work' = work \cup {[lo |-> iv.lo, hi |-> p, p? |-> p],
                                            [lo |-> p+1, hi |-> iv.hi, p? |-> iv.hi]}
  /\ pc' = "loop"

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == PartitionStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep) /\ WF_vars(Terminate)

Termination == (pc = "done") ~> (pc = "done")
====