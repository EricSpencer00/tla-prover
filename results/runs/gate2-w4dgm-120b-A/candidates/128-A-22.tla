---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* Bounded-length sequences: a finite version of Seq so the model stays
\* checkable.  The .cfg redefines Seq to be this, keeping FiniteSets and Naturals.
LimitedSeq == [n \in 0..MaxSeqLen |-> UNION { {k} \X (1..n) }]

\* A domain automorphism: a bijection on indices 1..n, represented as a set of
\* pairs so it can be used with relational composition.
OnetoOne(n) ==
  { f \in [1..n -> 1..n] :
      \A x \in 1..n : \A y \in 1..n : (f[x] = f[y]) => (x = y) }

VARIABLES seq, orig, todo, pc
vars == <<seq, orig, todo, pc>>

\* Every partition leaves elements outside the interval untouched, and the
\* two sides relative to the pivot are ordered correctly.
ValidPartitions(s, t, a, b) ==
  /\ s[a] <= s[b]
  /\ \A i \in 1..Len(s) :
       (i < a \/ i > b) => (s[i] = t[i])
  /\ \A i, j \in 1..Len(s) :
       (i <= a /\ j > b) => (t[i] <= t[j])

TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ todo \subseteq [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in { x \in Values^n : 1 <= n <= MaxSeqLen } :
       /\ seq = s
       /\ orig = s
  /\ todo = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

PartitionStep ==
  /\ pc = "loop"
  /\ \E a \in todo :
       /\ Len(seq) >= a.hi
       /\ IF a.lo = a.hi
          THEN todo' = todo \ {a}
          ELSE \E p \in a.lo..a.hi :
                 /\ \E s \in { t \in LimitedSeq :
                                  ValidPartitions(seq, t, a.lo, a.hi) } :
                      seq' = s
                 /\ todo' = (todo \ {a})
                            \cup {[lo |-> a.lo, hi |-> p]}
                            \cup {[lo |-> p + 1, hi |-> a.hi]}
       /\ pc' = IF (todo \ {a}) = {}
                  THEN "done" ELSE pc
  /\ orig' = orig

Done ==
  /\ pc = "done"
  /\ pc' = pc
  /\ UNCHANGED <<seq, orig, todo>>

Next == PartitionStep \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep)

\* At termination the output is a permutation of the input and is sorted.
PCorrect ==
  /\ (pc = "done") => (seq \in OnetoOne(Len(seq)) @@ orig)
  /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

TheoreticalBound ==
  (pc = "done") => (Len(seq) <= Len(orig))

\* The partition step refines relative sortedness between adjacent intervals.
Inv == TheoreticalBound
====