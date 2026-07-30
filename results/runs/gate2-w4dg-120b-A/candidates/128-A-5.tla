---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen, Seq

\* An interval is a contiguous range of indices of the sequence.
Interval == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

\* Two intervals are adjacent if they butt up against each other with no
\* overlap and no gap; this is the ordering the invariant works over.
Adjacent(i1, i2) ==
  \/ (i1.hi + 1 = i2.lo /\ i1.lo <= i1.hi /\ i2.lo <= i2.hi)
  \/ (i2.hi + 1 = i1.lo /\ i2.lo <= i2.hi /\ i1.lo <= i1.hi)

\* An automorphism of the domain is a bijection that preserves adjacency;
\* any permutation of the sequence can be written as composition with one.
DomAuto(f) ==
  /\ \A x \in 1..MaxSeqLen : f[x] \in 1..MaxSeqLen
  /\ \A x \in 1..MaxSeqLen : \A y \in 1..MaxSeqLen : f[x] = f[y] => x = y
  /\ \A i1, i2 \in 1..MaxSeqLen : Adjacent([lo |-> i1, hi |-> i1], [lo |-> i2, hi |-> i2])
                              => Adjacent([lo |-> f[i1], hi |-> f[i1]], [lo |-> f[i2], hi |-> f[i2]])

DomainPartitions(dom) ==
  {f \in [1..MaxSeqLen -> 1..MaxSeqLen] : DomAuto(f) /\ \A x \in 1..MaxSeqLen : x \in dom => f[x] \in dom}

\* The partition operator leaves the rest of the sequence untouched while
\* making sure everything in the lower subinterval is no greater than
\* everything in the upper subinterval; it ranges over all such valid outcomes.
Part(ns, i, j) ==
  {ns' \in [1..MaxSeqLen -> Values] :
     /\ \A k \in 1..MaxSeqLen : k < i \/ k > j => ns'[k] = ns[k]
     /\ \A a \in i..j : \A b \in (j+1)..MaxSeqLen : ns'[a] <= ns'[b]}

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ work \subseteq Interval
  /\ pc \in {"loop", "done"}

Permutation(seq, base) ==
  \E f \in DomainPartitions(1..MaxSeqLen) : seq = [i \in 1..MaxSeqLen |-> base[f[i]]]

\* The invariant tracks three intertwined facts: intervals are disjoint and
\* together cover the whole domain, the sequence is always a permutation of
\* the original, and whenever two intervals stand side by side the entire
\* left one is no greater than the entire right one.
Inv ==
  /\ \A i1 \in work : \A i2 \in work : i1 # i2 => (i1.hi < i2.lo \/ i2.hi < i1.lo)
  /\ \E lo, hi \in 1..MaxSeqLen :
       /\ \A i \in work : lo <= i.lo /\ i.hi <= hi
       /\ \A k \in 1..MaxSeqLen : (k < lo \/ k > hi) => seq[k] = orig[k]
  /\ \A i1 \in work : \A i2 \in work : Adjacent(i1, i2) => \A a \in i1.lo..i1.hi : \A b \in i2.lo..i2.hi : seq[a] <= seq[b]

Init ==
  /\ seq = Seq
  /\ orig = Seq
  /\ work = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "loop"

Loop ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E i \in work :
       /\ work' = IF i.lo = i.hi THEN work \ {i}
          ELSE \E j \in i.lo..i.hi :
                 /\ seq' \in Part(seq, i.lo, j)
                 /\ work' = (work \ {i}) \cup {[lo |-> i.lo, hi |-> j], [lo |-> j+1, hi |-> i.hi]}
       /\ UNCHANGED <<orig, pc>>

Done ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Loop \/ Done \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

\* When the algorithm terminates it has sorted the original input.
PCorrect ==
  (pc = "done") => (\A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i+1])

AdditionalAssumption == Values \subseteq Nat

Termination == (pc = "done") ~> (pc = "loop")

====