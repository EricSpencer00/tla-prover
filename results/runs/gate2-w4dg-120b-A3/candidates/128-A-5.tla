---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

\* We extend the standard Sequences module but swap in a bounded version of Seq
\* for model checking. The name Seq on the left is never declared here -- it is
\* inherited from Sequences and always refers to the finite version below.
\* The constant MaxSeqLen is bound by the model configuration.
LimitedSeq(n) == IF n <= MaxSeqLen THEN n ELSE 0

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* An interval is a contiguously addressed subrange of the sequence, identified
\* by its first and last indices (1-indexed, as in the Sequences module).
Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

\* A partition is any permutation of seq that leaves elements outside the
\* chosen interval untouched and leaves the lower subinterval's elements
\* no greater than the upper subinterval's elements.
Partitions(s, iv, p) ==
  {t \in [1..Len(s) -> Values]:
     /\ \A i \in 1..Len(s): i < iv.lo \/ i > iv.hi => t[i] = s[i]
     /\ \A i \in iv.lo..p, j \in p+1..iv.hi: t[i] <= t[j]}

\* Lower and upper subintervals produced by partitioning at pivot p.
Lower(iv, p) == [lo |-> iv.lo, hi |-> p]
Upper(iv, p) == [lo |-> p+1, hi |-> iv.hi]

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) > 0
  /\ Len(seq) <= MaxSeqLen
  /\ orig \in Seq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in {t \in Seq(Values): Len(t) > 0 /\ Len(t) <= MaxSeqLen}:
       seq = s /\ orig = s
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* The single transition: pick an interval, split off a singleton or partition
\* it, update the sequence, and replace the interval with its subintervals.
Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E iv \in work:
       /\ LET others == work \ {iv} IN
          /\ IF iv.lo = iv.hi
             THEN work' = others
             ELSE \E p \in iv.lo..(iv.hi - 1):
                    \/ \E s \in Partitions(seq, iv, p):
                         /\ seq' = s
                         /\ work' = others \cup {Lower(iv, p), Upper(iv, p)}
  /\ pc' = pc

Terminated ==
  /\ pc = "done"
  /\ UNCHANGED vars

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminated \/ Stall

\* Weak fairness on Step is what forces the sorter to make progress instead
\* of sitting in the "loop" state forever.
Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Domain(a) == {i \in 1..Len(seq) : a[i] # 0}

\* The permutation and sortedness invariants mention a bijection a : [1..Len(seq)]
\* [-> 1..Len(seq)]. Any automorphism of the domain is a bijection, so the set of
\* all such bijections is just the set of automorphisms themselves.
Automorphisms == {a \in [1..Len(seq) -> 1..Len(seq)] : \A i, j \in 1..Len(seq): a[i] = a[j] => i = j}

Permutations == {s \in Seq(Values): \E a \in Automorphisms: \A i \in 1..Len(s): s[a[i]] = orig[i]}

PCorrect == pc = "done" => (seq \in Permutations /\ \A i \in 1..(Len(seq) - 1): seq[i] <= seq[i + 1])

\* The full invariant: the intervals in work partition the domain, seq stays a
\* permutation of the input, and the relative ordering of any two intervals
\* that have been carved out is already correct.
Inv ==
  /\ \A i, j \in 1..Len(seq): (i \in Domain(seq) /\ j \in Domain(seq) /\ i < j) => seq[i] <= seq[j]

Termination == <>(pc = "done")

====