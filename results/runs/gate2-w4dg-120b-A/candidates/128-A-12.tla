---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

NoWork == work = {}

Intervals == SUBSET (1 .. Len(seq) \X (1 .. Len(seq)))

Iota(n) == IF n = 0 THEN << >> ELSE << n >>

NaturallySorted(s) ==
  \A i \in 1 .. Len(s) - 1 : s[i] <= s[i + 1]

\* The partition operator produces all permutations that leave elements outside
\* the interval unchanged, while forcing the left side of the pivot to be
\* less-than-or-equal-to everything on the right side of the pivot.
RECURSIVE Partitions(_, _, _)
Partitions(sq, lo, hi) ==
  IF lo > hi THEN {}
  ELSE IF lo = hi THEN {sq}
  ELSE
    {t \in (Values) ^ Len(sq) :
        /\ \A i \in 1 .. Len(sq) : (i < lo \/ i > hi) => t[i] = sq[i]
        /\ \A i \in lo .. hi, j \in lo .. hi :
             (i <= j) => t[i] <= t[j]}

Automorphisms(k) == {f \in [1 .. k -> 1 .. k] : \A i, j \in 1 .. k : (i = j) <=> (f[i] = f[j])}
\* A permutation of a sequence: reindex via a domain automorphism.
Permutations(sq) ==
  {sq[f[1]], sq[f[2]], ..., sq[f[Len(sq)]] : f \in Automorphisms(Len(sq))}

TypeOK ==
  /\ seq \in (\X Values) ^ (1 .. MaxSeqLen)
  /\ orig \in (\X Values) ^ (1 .. MaxSeqLen)
  /\ Len(seq) > 0
  /\ work \subseteq Intervals
  /\ pc \in {"main", "done"}

Init ==
  /\ seq \in Permutations(Seq)
  /\ orig \in Permutations(Seq)
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "main"

\* The only action: one iteration of the sorting loop, which either removes a
\* singleton interval or (nondeterministically) picks a pivot, partitions the
\* interval, and replaces it with the two new intervals.
Step ==
  /\ pc = "main"
  /\ \E i \in work :
       /\ work' = work \ {i}
       /\ IF i[1] = i[2]
          THEN work'
          ELSE
            \E p \in i[1] .. i[2] :
              /\ \E t \in Partitions(seq, i[1], i[2]) :
                   /\ \A i1 \in i[1] .. p, j \in p + 1 .. i[2] : t[i1] <= t[j]
                   /\ seq' = t
              /\ work' = work' \cup {<<i[1], p>>, <<p + 1, i[2]>>}
  /\ pc' = IF pc = "main" /\ NoWork THEN "done" ELSE pc

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Stall

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)

PCorrect ==
  pc = "done" => (seq = orig /\ NaturallySorted(seq))

\* Partition the domain into sorted-unprocessed, sorted-processed, and
\* unprocessed subintervals that are still pairwise disjoint.
Inv ==
  /\ work \subseteq Intervals
  /\ \E lo, hi \in 1 .. Len(seq) :
       /\ lo <= hi
       /\ (lo = 1 \/ \E i \in lo .. hi : i + 1 \notin lo .. hi)
       /\ (hi = Len(seq) \/ \E i \in lo .. hi : i - 1 \notin lo .. hi)
  /\ seq \in Permutations(orig)
  /\ NaturallySorted(seq)

Termination == <>(pc = "done")
====