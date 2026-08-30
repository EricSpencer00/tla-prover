---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* INTERVALS: contiguous index ranges in the sequence; SEQPOOL: all sequences
\* over the allowed value set up to the bounded model-checking length.
Intervals == [i: 1..MaxSeqLen, j: 1..MaxSeqLen]
SEQUENCE == UNION { (1..n -> Values) : n \in 1..MaxSeqLen }
SEQPREFIX == UNION { (1..n -> Values) : n \in 1..MaxSeqLen }

\* Permutations: composed with automorphisms of the domain.
Permutations(s) == { g \circ s : g \in [1..MaxSeqLen -> 1..MaxSeqLen] : \A x \in 1..MaxSeqLen : g[x] \in 1..MaxSeqLen }

\* Partition(s, i, j): all permutations of s that leave indices outside
\* [i, j] untouched while respecting the pivot ordering.
Partition(s, i, j) ==
  { g \circ s : g \in Permutations(s) :
      \A x \in 1..MaxSeqLen : (x < i \/ x > j) => g[x] = x
      \A x \in i..j : \A y \in i..j : (x <= i /\ y >= j) => g[x] <= g[y] }

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

TypeOK ==
  /\ seq \in SEQUENCE
  /\ original \in SEQUENCE
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in SEQPREFIX : seq = original = s
  /\ work = {[i |-> 1, j |-> Len(seq)]}
  /\ pc = "loop"

\* One iteration: pick an interval, partition it around a pivot, and split it.
Step ==
  /\ pc = "loop"
  /\ \E int \in work :
       /\ work' = work \ {int}
       /\ IF int.i = int.j
          THEN work' = work'
          ELSE \E pivot \in int.i..int.j :
                 /\ seq' = CHOOSE s \in Partition(seq, int.i, int.j) :
                              \A x \in 1..MaxSeqLen : (x < int.i \/ x > int.j) => s[x] = seq[x]
                 /\ work' = work' \cup
                              {[i |-> int.i, j |-> pivot], [i |-> pivot + 1, j |-> int.j]}
  /\ pc' = IF work' = {} THEN "done" ELSE "loop"

Done ==
  /\ pc = "done"
  /\ pc' = pc
  /\ UNCHANGED <<seq, original, work>>

Next == Step \/ Done

\* Program counter that is never stuck on the loop is the termination
\* witness; WF makes the partitioning step strongly fair.
Spec == Init /\ [][Next]_vars
  /\ WF_vars(Step) /\ WF_vars(Done)
  /\ \A int \in Intervals : SF_vars(\E s \in Partition(seq, int.i, int.j) : seq' = s)

\* The full invariant: subintervals partition the domain, the sequence is
\* always a permutation of the input, and the two halves stay ordered.
Inv ==
  /\ (Len(seq) = Len(original)
       /\ {1..Len(seq)} = {1..Len(original)}
       /\ \A x \in 1..Len(seq) : \E y \in 1..Len(original) : seq[x] = original[y]
       /\ \E g \in [1..Len(seq) -> 1..Len(original)] :
            \A x \in 1..Len(seq) : seq[x] = original[g[x]])
  /\ \A int \in Intervals :
       /\ int.i <= int.j => (int.j <= Len(seq) /\ int.i >= 1)
       /\ int.j < Len(seq) => seq[int.j] <= seq[int.j + 1]

\* Termination is a property about the reachable state space, not a stub.
Termination == <>(pc = "done")
PCorrect == pc = "done" => (seq = original /\ \A i \in 1..Len(seq) - 1 : seq[i] <= seq[i + 1])
TypeOK == TypeOK

\* The bounded operator that replaces Sequences.Seq for model checking.
LimitedSeq == [i \in 1..MaxSeqLen |-> seq[i]]

====