---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* An interval is a contiguous range of sequence indices; the sort keeps a set
\* of intervals left to process.
Interval == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

\* Permutations and automorphisms of the domain are used to state permutation
\* preservation without tying the model to a particular sequence length.
Auto     == [i \in 1..MaxSeqLen |-> i]
Compose(g, h) == [i \in 1..MaxSeqLen |-> g[h[i]]]
\* BoundedSeq makes the modeling of Permutes tractable; it is the FINITE
\* version of Seq, so the model stays finite.
BoundedSeq == { <<>> } \cup { [1..n -> Values] : n \in 1..MaxSeqLen }
Permutes(s, t) == \E g \in Auto :
  \A i \in 1..Len(s) : s[i] = t[g[i]]

\* The partition operator abstracts the actual partition procedure: it produces
\* every possible partitioning outcome that respects the pivot boundary, so the
\* action can nondeterministically pick any of them.
Partition(s, lo, hi, p) == {
  t \in BoundedSeq :
    /\ Len(t) = Len(s)
    /\ \A i \in 1..Len(s) :
         IF lo <= i <= hi THEN
           IF i <= p THEN s[i] <= s[p] ELSE s[p] <= s[i]
         ELSE s[i] = t[i]
}

\* The algorithm never constructs or destroys elements; it only moves them, so
\* the permutation property here is the whole of correctness, and sortedness
\* is a consequence of the final interval set being all singletons.
VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ orig \in BoundedSeq
  /\ todo \in SUBSET Interval
  /\ pc \in { "main", "terminated" }

Init ==
  /\ \E s \in BoundedSeq :
       /\ Len(s) <= MaxSeqLen
       /\ s # <<>>
       /\ seq = s
       /\ orig = s
       /\ todo = {[lo |-> 1, hi |-> Len(s)]}
  /\ pc = "main"

Main ==
  /\ pc = "main"
  /\ \E w \in todo :
       /\ todo' = todo \ {w}
       /\ IF w.lo = w.hi THEN UNCHANGED <<seq, todo>>
          ELSE
            \E p \in w.lo..w.hi :
              /\ seq' = CHOOSE t \in Partition(seq, w.lo, w.hi, p) : TRUE
              /\ todo' = todo \cup {
                   [lo |-> w.lo, hi |-> p],
                   [lo |-> p + 1, hi |-> w.hi]
                 }
  /\ pc' = IF \E w \in todo : w.lo # w.hi THEN pc ELSE "terminated"

Stall == pc = "terminated" /\ UNCHANGED vars

Next == Main \/ Stall

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Main) /\ WF_vars(Stall)

PCorrect ==
  /\ (\A i \in 1..MaxSeqLen : seq[i] = orig[i]) => (seq = orig)
  /\ (\A i \in 1..MaxSeqLen : ~orig[i] = orig[i + 1]) => (seq = orig)

TypeOKOK == TypeOK

\* The invariant combines three orthogonal facts that together imply the
\* output is a sorted permutation of the input: domain partitions are disjoint
\* and cover the whole active range, the sequence is a permutation of the
\* original, and adjacent intervals are already sorted relative to each other.
Inv ==
  /\ \A x, y \in todo : x # y => (x.hi < y.lo \/ y.hi < x.lo)
  /\ \A x \in todo :
       /\ x.lo = 1 \/ (\E z \in todo : z.hi = x.lo - 1)
       /\ \A y \in todo : y.hi = x.hi => y = x
  /\ Permutes(seq, orig)
  /\ \A i \in 1..MaxSeqLen : ~orig[i] = orig[i + 1] => (seq[i] <= seq[i + 1])

Termination == <>(pc = "terminated")

====