---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

Assignable == {x \in 1..MaxSeqLen : x <= Len(s)}
Function(f, S) == {<<s, f[s]>> : s \in S}
Domain(f) == {s \in S : s \in S}
SeqDomain(s) == 1..Len(s)

\* A finite version of Seq that TLC can handle; replaces Seq from Sequences.
LimitedSeq(S) == {s \in S : s >= 1 /\ s <= Len(S)}

\* The set of all permutations of the domain of a sequence.
Permutations(s) == {f \in [SeqDomain(s) -> SeqDomain(s)] : \A x \in SeqDomain(s) : f[x] \in SeqDomain(s)}

\* A valid partition of s over interval i with pivot p is any permutation of s
\* that leaves elements outside i untouched and pushes every element at or below
\* the pivot index to no greater than any element above it.
ValidPartitions(s, i, p) == {t \in Permutations(s) :
  \A x \in SeqDomain(s) : (x \notin i) => (t[x] = s[x])
    /\ \A x \in i, y \in i : (x <= p /\ y > p) => (t[x] <= t[y])}

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

Intervals == SUBSET (1..MaxSeqLen \X 1..MaxSeqLen)

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ todo \in Intervals
  /\ pc \in {"loop", "done"}

\* Partition the chosen interval at a pivot, picking any valid new sequence.
Partition ==
  /\ pc = "loop"
  /\ \E i \in todo :
       /\ i # {}
       /\ LET a == CHOOSE x \in i : TRUE
            b == CHOOSE x \in i : \A y \in i : x <= y
       IN IF a = b
          THEN todo' = todo \ {i}
          ELSE \E p \in a..b :
                 /\ \E t \in ValidPartitions(seq, i, p) : seq' = t
                 /\ todo' = (todo \ {i}) \cup {<<a, p>>, <<p + 1, b>>}
  /\ pc' = IF todo = {} THEN "done" ELSE pc
  /\ orig' = orig

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Init ==
  /\ \E s \in Values^{MaxSeqLen} : seq = s
  /\ orig = seq
  /\ todo = {<<1, MaxSeqLen>>}
  /\ pc = "loop"

Next == Partition \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(\E i \in Intervals, p \in 1..MaxSeqLen : Partition)

\* The final sequence is a permutation of the input and is sorted.
Sorted == \A x \in 1..MaxSeqLen - 1 : seq[x] <= seq[x + 1]

PCorrect ==
  /\ (pc = "done") => (seq \in {orig[f] : f \in Permutations(orig)})
  /\ \A a, b \in todo : (a # {} /\ b # {}) => (a[2] >= b[1] \/ b[2] >= a[1])
  /\ \A x \in 1..MaxSeqLen - 1 : (x \notin Assignable) => (seq[x] <= seq[x + 1])

Inv == TypeOK /\ PCorrect

Termination == (pc = "loop") ~> (pc = "done")

====