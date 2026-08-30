---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Automorphisms

CONSTANTS Values, MaxSeqLen

\* Dominates is the partition consistency relation; it is the core of the
\* correctness claim about the single-step partition operator.
Dominates(v, w) == v <= w /\ w \notin Values /\ v \notin Values

VARIABLES seq, orig, worklist, pc

vars == <<seq, orig, worklist, pc>>

Intervals == UNION {[1..n -> Values] : n \in 0..MaxSeqLen}
SeqDomain == UNION {[1..n -> Values] : n \in 1..MaxSeqLen}

\* Stuttering after termination; always present so the spec never deadlocks.
Stall == [seq |-> seq, orig |-> orig, worklist |-> worklist, pc |-> pc]

TypeOK ==
  /\ seq \in Intervals
  /\ orig \in Intervals
  /\ worklist \subseteq (1..MaxSeqLen) \X (1..MaxSeqLen)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in SeqDomain :
       /\ seq = s
       /\ orig = s
  /\ worklist = {<<1, Len(seq>>}
  /\ pc = "loop"

\* The nondeterministic choice is the abstracted partition step: any
\* sequence that dominates the low side over the interval and touches
\* nothing outside it is a valid result of a real partition procedure.
Partition(s, lo, hi, k) ==
  /\ s \in SeqDomain
  /\ Len(s) = Len(seq)
  /\ \A i \in 1..Len(s) : (i < lo \/ i > hi) => s[i] = seq[i]
  /\ \A i \in lo..k, j \in (k + 1)..hi : Dominates(s[i], s[j])

Step ==
  /\ pc = "loop"
  /\ \E p \in worklist :
       /\ worklist' = worklist \ {p}
       /\ IF p[1] = p[2]
          THEN seq' = seq
          ELSE \/ \E k \in p[1]..p[2] :
                  \E s \in SeqDomain :
                    /\ Partition(s, p[1], p[2], k)
                    /\ seq' = s
               /\ worklist' = worklist \cup {<<p[1], k>>, <<k + 1, p[2]>>}
  /\ pc' = IF worklist = {} THEN "done" ELSE pc
  /\ orig' = orig

Next == Step \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

PCorrect == pc = "done" => (\A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* The partition operator preserves the multiset of values in the interval
\* it touched, which is what makes permuting external values impossible.
Permutation(x, y) == \E g \in Aut(Domain(x)) : y = x \circ g
Inv ==
  /\ (\A p, q \in worklist : (p[1] <= q[2] /\ q[1] <= p[2]) => (p = q \/ p[2] < q[2] \/ q[1] < p[1]))
  /\ Permutation(seq, orig)
  /\ (\A p, q \in worklist : p[2] < q[1] => \A j \in p[2] + 1..q[1] - 1 : 1 <= j <= Len(seq))

Termination == <>(pc = "done")

\* Redefine Seq, which comes from Sequences, as a bounded version so the
\* model stays finite; this is what the .cfg file replaces it with.
LimitedSeq ==
  { s \in SeqDomain : Len(s) <= MaxSeqLen }
====