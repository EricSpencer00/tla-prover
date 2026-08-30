---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS Values, MaxSeqLen

\* A finite version of Seq that truncates out-of-range indices to 0 (unused)
LimitedSeq(seq, i) == IF ~ (1 <= i /\ i <= Len(seq)) THEN 0 ELSE seq[i]

Intervals == (1..MaxSeqLen) \X (1..MaxSeqLen)

VARIABLES seq, orig, todo, pc
vars == <<seq, orig, todo, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ todo \subseteq Intervals
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in Seq(Values) : seq = s
  /\ orig = seq
  /\ todo = {(1, Len(seq))}
  /\ pc = "main"

\* A valid partition step: subintervals are correct subranges and the new
\* sequence is a permutation that respects the pivot ordering.
Partition(i, j, p) ==
  /\ p \in [1..j]
  /\ i <= p /\ p <= j
  /\ \E ns \in [Seq(Values) -> BOOLEAN] :
       /\ ns(seq)
       /\ \A k \in 1..MaxSeqLen : (k < i \/ k > j) => LimitedSeq(ns, k) = LimitedSeq(seq, k)
       /\ \A a \in i..p, b \in p+1..j : LimitedSeq(ns, a) <= LimitedSeq(ns, b)
  /\ seq' = ns
  /\ todo' = (todo \ {(i, j)}) \cup {(i, p), (p+1, j)}

Step ==
  /\ pc = "main"
  /\ \E i, j \in 1..MaxSeqLen :
       /\ <<i, j>> \in todo
       /\ IF i = j THEN todo' = todo \ {<<i, j>>} /\ UNCHANGED seq
          ELSE \E p \in 1..j : Partition(i, j, p)
  /\ UNCHANGED <<orig, pc>>

Terminate ==
  /\ pc = "main"
  /\ todo = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, todo>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* The sorted result is a permutation of the input and is non-decreasing.
Sorted == \A i \in 1..(Len(seq) - 1) : LimitedSeq(seq, i) <= LimitedSeq(seq, i + 1)
Permutation ==
  \E f \in [1..Len(seq) -> 1..Len(seq)] :
    /\ \A a, b \in 1..Len(seq) : f[a] = f[b] => a = b
    /\ \A i \in 1..Len(seq) : LimitedSeq(seq, f[i]) = LimitedSeq(orig, i)

PCorrect == (pc = "done") => (Sorted /\ Permutation)

\* An inductive shape that any valid partition must preserve.
SortedWithinIntervals ==
  \A i, j \in 1..MaxSeqLen : (<<i, j>> \in todo) => \A a \in i..j-1, b \in a+1..j : LimitedSeq(seq, a) <= LimitedSeq(seq, b)
TypeOKInv == TypeOK / Inv == SortedWithinIntervals

Termination == (pc = "main") ~> (pc = "done")
====