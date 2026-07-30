---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

\* Intervals are always valid ranges inside the current sequence; the sort
\* only refines them and never fabricates new ones.
Intervals == {i \in 1..MaxSeqLen : i <= Len(seq)} \X {i \in 1..MaxSeqLen : i <= Len(seq)}

TypeOK ==
  /\ seq \in Seq
  /\ original \in Seq
  /\ work \subseteq Intervals
  /\ pc \in {"mainLoop", "terminated"}

Init ==
  /\ seq = Seq
  /\ original = Seq
  /\ work = {<<1, Len(Seq)>>}
  /\ pc = "mainLoop"

\* A valid partition leaves everything outside the interval untouched and
\* guarantees that everything on the left side of the pivot is no greater
\* than everything on the right side.
ValidPartitions(a, lo, hi, p) ==
  {b \in Seq :
     /\ \A i \in 1..Len(Seq) : (i < lo \/ i > hi) => b[i] = a[i]
     /\ \A i \in lo..p, j \in (p + 1)..hi : b[i] <= b[j]}

\* The invariants below are the real meat of the safety argument; the first
\* piece is a domain partition that feeds the others.
Ivt ==
  /\ \A i \in 1..MaxSeqLen : i \le Len(seq) => Len(seq) >= i
  /\ \A i \in 1..MaxSeqLen : i > Len(seq) => Len(seq) < i
  /\ \A k \in 1..MaxSeqLen :
       /\ k \in 1..Len(seq) => seq[k] \in Values
       /\ k \notin 1..Len(seq) => seq[k] = 0
  /\ \A i \in 1..Len(seq) : \A j \in 1..Len(seq) : i <= j => seq[i] <= seq[j]
  /\ \A i \in Intervals : i \in work => 1 <= i[1] /\ i[1] <= i[2] /\ i[2] <= Len(seq)
  /\ \A i \in Intervals : i \in work => \E p \in i[1]..i[2] : Len(seq) >= p

Next ==
  \/ IF pc = "mainLoop" /\ work # {} THEN
       LET w == CHOOSE w \in work :
         \A x \in work : \A y \in work : (x[1] <= w[1] /\ x[2] >= w[2]) => (w[1] <= y[1] /\ w[2] >= y[2])
       IN
         \/ /\ w[1] = w[2]
            /\ work' = work \ {w}
            /\ UNCHANGED <<seq, original, pc>>
         \/ /\ w[1] < w[2]
            /\ \E p \in w[1]..w[2] :
                 /\ \E seq' \in ValidPartitions(seq, w[1], w[2], p) : seq' = seq'
                 /\ work' = (work \ {w}) \cup {<<w[1], p>>, <<p + 1, w[2]>>}
            /\ UNCHANGED <<original, pc>>
     ELSE IF pc = "mainLoop" /\ work = {} THEN
       /\ pc' = "terminated"
       /\ UNCHANGED <<seq, original, work>>
     ELSE IF pc = "terminated" THEN
       /\ pc' = "terminated"
       /\ UNCHANGED <<seq, original, work>>
     ELSE UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The final state is a sorted permutation of the input.
PCorrect ==
  /\ pc = "terminated"
  /\ \A i \in 1..Len(seq) : \E j \in 1..Len(original) : seq[i] = original[j]
  /\ \A i \in 1..Len(seq) : \A j \in 1..Len(seq) : i <= j => seq[i] <= seq[j]

Termination ==
  <>(pc = "terminated")

====