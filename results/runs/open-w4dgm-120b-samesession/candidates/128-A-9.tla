---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The model checks a bounded-length version; the real operator is the
\* standard (infinite) Seq from Sequences, but that is not checkable.
LimitedSeq(S) == CHOOSE f \in [1..Len(S) -> Values] :
  \A i \in 1..Len(S) : f[i] = S[i]

Variables seq, origSeq, work, pc

Intervals == {r \in 1..MaxSeqLen \X 1..MaxSeqLen : r[1] <= r[2]}

\* Split an interval at a pivot index; the result is two non-empty intervals.
Split(r, i) ==
  LET lo == <<r[1], i>>
      hi == <<i + 1, r[2]>>
  IN IF lo[1] <= lo[2] /\ hi[1] <= hi[2] THEN {lo, hi} ELSE {}

\* A partition of seq[r] about pivot i, leaving all other indices unchanged.
Partition(x, r, i) ==
  {y \in [1..MaxSeqLen -> Values] :
     /\ \A k \in 1..MaxSeqLen : (k < r[1] \/ k > r[2]) => y[k] = x[k]
     /\ \A a \in r[1]..i, b \in (i + 1)..r[2] : y[a] <= y[b]}

\* A sub-permutation of x: a bijection that reorders some domain subset.
Permutation(x, y) ==
  \E g \in [1..MaxSeqLen -> 1..MaxSeqLen] :
    /\ \A i \in 1..MaxSeqLen : g[i] <= Len(x)
    /\ \A i, j \in 1..MaxSeqLen :
         (g[i] <= Len(x) /\ g[i] = g[j]) => i = j
    /\ \A i \in 1..Len(x) : \E j \in 1..MaxSeqLen : g[j] = i /\ y[j] = x[i]

RECURSIVE SubSeq(_)
SubSeq(S) ==
  IF S = {} THEN {}
  ELSE LET r == CHOOSE e \in S : TRUE
           rest == SubSeq(S \ {r})
       IN IF r[1] > r[2] THEN rest
          ELSE SubSeq(S \ {r}) \cup {r[1] .. r[2]}

\* Every interval covers a gap-free segment of its domain, and any two
\* intervals are either nested or disjoint: this is exactly what makes the
\* whole set a partition of the domain.
DisjointCovering ==
  /\ \A r \in work : r[1] <= r[2]
  /\ \A r1, r2 \in work :
       r1[1] <= r1[2] /\ r2[1] <= r2[2] => (r1 \subseteq r2 \/ r2 \subseteq r1 \/ r1 \cap r2 = {})

SortedWithin(r) ==
  \A a, b \in r[1]..r[2] : seq[a] <= seq[b]

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ origSeq \in [1..MaxSeqLen -> Values]
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in (Values \X Values) \X (Values \X Values) # {} :
       seq = LimitedSeq(s)
  /\ origSeq = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "loop"

Next ==
  \/ \E r \in work, i \in r[1]..r[2] :
       /\ pc = "loop"
       /\ \E y \in Partition(seq, r, i) :
            /\ seq' = y
            /\ work' = (work \ {r}) \cup Split(r, i)
       /\ UNCHANGED <<origSeq, pc>>
  \/ /\ pc = "loop"
       /\ work = {}
       /\ pc' = "done"
       /\ UNCHANGED <<seq, origSeq, work>>
  \/ /\ pc = "done"
       /\ UNCHANGED <<seq, origSeq, work, pc>>

Spec ==
  /\ Init /\ [][Next]_<<seq, origSeq, work, pc>>
  /\ WF_vars(Next)

PCorrect == pc = "done" => (\A i \in 1..MaxSeqLen : seq[i] <= seq[i + 1])

Inv == DisjointCovering /\ \A r \in work : SortedWithin(r)

Termination == <>(pc = "done")

====