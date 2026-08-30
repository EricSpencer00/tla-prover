---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* Finite, bounded sequences: a model-checkable version of Seq, overriding the
\* standard definition from Sequences (the .cfg names the operator to replace).
LimitedSeq(i) == CHOOSE s \in Seq(Vals) : Len(s) = i

\* An automorphism of the domain 1..n: a bijection on positions, used to define
\* permutation equivalence between sequences of the same length.
Bijection(n, f) == /\ DOMAIN f = 1..n /\ RANGE f = 1..n
                    /\ \A x, y \in 1..n : f[x] = f[y] => x = y

Permutation(n, a, b) ==
  \E f \in [1..n -> 1..n] : Bijection(n, f) /\ \A i \in 1..n : b[i] = a[f[i]]

\* The partition operator: a family of result sequences for each interval and
\* pivot. It only ever reorders elements inside the chosen interval, keeping
\* elements at or below the pivot index no greater than those above it.
RECURSIVE PartitionSeq(_, _, _)
PartitionSeq(s, i, j) ==
  IF i = 1 THEN {s}
  ELSE IF j = Len(s) THEN {s}
  ELSE { s \in Seq(Vals) :
           /\ (\A k \in 1..i : s[k] = PartitionSeq(s, i, j)[k])
           /\ (\A k \in j+1..Len(s) : s[k] = PartitionSeq(s, i, j)[k])
           /\ \A k \in i+1..j : PartitionSeq(s, i, j)[k] <= s[j] }

\* Intervals in the work set are processed in any order, so sorting is
\* only guaranteed across interval boundaries if the partition relation is
\* transitive across its own generated reorderings -- exactly the property
\* the invariant with CrossSorted below checks.
Interval == [lb : 1..MaxSeqLen, ub : 1..MaxSeqLen]

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in Seq(Vals)
  /\ orig \in Seq(Vals)
  /\ work \subseteq Interval
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in { t \in LimitedSeq(i) : i \in 1..MaxSeqLen } : seq = s /\ orig = s
  /\ work = {[lb |-> 1, ub |-> Len(seq)]}
  /\ pc = "main"

\* Main action: partition an interval and replace it by two subintervals.
Partition ==
  /\ pc = "main"
  /\ work # {}
  /\ \E it \in work :
       /\ work' = work \ {it}
       /\ IF it.lb = it.ub
          THEN work' = work'
          ELSE
            /\ \E p \in it.lb..it.ub :
                 /\ seq' \in PartitionSeq(seq, it.lb - 1, p)
                 /\ work' = work' \cup {[lb |-> it.lb, ub |-> p], [lb |-> p+1, ub |-> it.ub]}
            /\ UNCHANGED orig
  /\ pc' = IF work' = {} THEN "done" ELSE pc

Stall == pc = "done" /\ UNCHANGED vars

Next == Partition \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Partition)

\* The three-part invariant: domains stay partitioned, every step is a
\* permutation of the original, and each interval is internally sorted.
Inv ==
  /\ \A a \in work, b \in work : a.lb = b.lb => a.ub = b.ub
  /\ Permutation(Len(orig), orig, seq)
  /\ \A it \in work : \A i \in it.lb..it.ub-1 : seq[i] <= seq[i+1]

\* Termination is the only liveness property; the rest is safety.
Termination == <> (pc = "done")

PCorrect == pc = "done" => Permutation(Len(orig), orig, seq) /\ \A i \in 1..Len(seq)-1 : seq[i] <= seq[i+1]
TypeOKInv == TypeOK /\ Inv
====