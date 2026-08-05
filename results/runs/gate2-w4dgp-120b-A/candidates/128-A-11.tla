---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == {[lo, hi] \in 0..MaxSeqLen \X 0..MaxSeqLen : lo <= hi}
Automorphisms == {f \in [0..MaxSeqLen -> 0..MaxSeqLen] : \A i \in 0..MaxSeqLen : f[i] \in 0..MaxSeqLen}
IsPermutation(f) == f \in Automorphisms
Permutations(s) == {s \o f : f \in Automorphisms}
Sorted(s) == \A i \in 1..Len(s) - 1 : s[i] <= s[i + 1]

LimitedSeq == {s \in Seq(Values) : Len(s) <= MaxSeqLen}

Partitioned(xs, i, k) == {ys \in Permutations(xs) :
  \A j \in 1..i : ys[j] <= xs[i + 1]
  /\ \A j \in i + 1..k : xs[i + 1] <= ys[j]
  /\ \A j \in k + 1..Len(xs) : ys[j] = xs[j]}

TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ seq # <<>>
  /\ work \subseteq Intervals
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in LimitedSeq : seq = s /\ orig = s
  /\ work = {[0, Len(seq)]}
  /\ pc = "main"

PartitionAndSplit ==
  /\ pc = "main"
  /\ work # {}
  /\ \E i \in work :
       IF i[1] = i[2] THEN
         work' = work \ {i}
         /\ UNCHANGED seq
       ELSE
         /\ \E k \in i[1]..i[2] :
              \E ys \in Partitioned(seq, k, i[2]) :
                /\ seq' = ys
                /\ work' = (work \ {i}) \cup {[i[1], k], [k + 1, i[2]]}
         /\ UNCHANGED <<orig, pc>>
  /\ pc' = "main"

Terminate ==
  /\ pc = "main"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == PartitionAndSplit \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionAndSplit) /\ WF_vars(Terminate)

PCorrect ==
  (pc = "done" => (seq ~ orig /\ Sorted(seq)))

DomainPart ==
  /\ \A i \in work : i[2] <= Len(seq)
  /\ \A i, j \in work : i # j => (i[1] >= j[2] \/ j[1] >= i[2])

Inv == DomainPart

Termination == <>(pc = "done")
====