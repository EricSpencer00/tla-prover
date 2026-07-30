---------------------------- MODULE Quicksort ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The original-plus-cal source, translated by the TLA+ toolbox into the
\* operators below. The translation of the PlusCal "sort" procedure is
\* exactly the set of transitions in the algorithm's loop.
\* The model also binds the original sequence to a variable so that
\* the permutation property can be stated after termination.

\* domain and interval notation
Domain == 1..MaxSeqLen
Intervals == SUBSET [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

\* the permutation operator: sigma is an automorphism of 1..MaxSeqLen
Permutation(s, sigma) == [i \in Domain |-> s[sigma[i]]]

\* a valid partition for a pivot position: elements inside the interval may
\* be reordered, but nothing moves across the pivot border.
ValidPartitions(s, lo, hi, p) ==
  {t \in [Domain -> Values] :
     \A i \in Domain :
       (i < lo \/ i > hi) => t[i] = s[i] /\ (lo <= i <= p) => \A j \in (p + 1)..hi : t[i] <= t[j]}

VARIABLES seq, orig, worklist, pc
vars == <<seq, orig, worklist, pc>>

TypeOK ==
  /\ seq \in [Domain -> Values]
  /\ orig \in [Domain -> Values]
  /\ worklist \subseteq Intervals
  /\ pc \in {"choice", "partition", "done"}

Init ==
  /\ \E s \in [Domain -> Values] :
       /\ \A i \in Domain : s[i] \in Values
       /\ seq' = s /\ orig' = s
  /\ worklist = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "choice"

\* One partition step, driven by the choice of pivot location.
PartitionStep ==
  /\ \E R \in worklist :
       /\ worklist' = worklist \ {R}
       /\ IF R.lo = R.hi
          THEN worklist' = worklist \ {R}
          ELSE
            /\ \E p \in R.lo..R.hi :
                 /\ \E seq' \in ValidPartitions(seq, R.lo, R.hi, p) : seq' = seq'
                 /\ worklist' = worklist \cup
                        { [lo |-> R.lo, hi |-> p], [lo |-> p + 1, hi |-> R.hi] }

Done ==
  /\ worklist = {}
  /\ pc = "choice"
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, worklist>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == PartitionStep \/ Done \/ Stall

Spec == Init /\ [][Next]_vars

\* The algorithm is a sorting algorithm, so the PCorrect invariant is only
\* meant to hold at termination -- the permutation is trivial while worklist
\* is non-empty, because the algorithm has not finished yet.
PCorrect ==
  (pc = "done") =>
    /\ \A f \in {f \in [Domain -> Domain] : \A i \in Domain : f[i] \in Domain} : seq = Permutation(orig, f)
    /\ \A i, j \in Domain : i <= j => seq[i] <= seq[j]

\* single-valuedness of seq and orig under all reachable states
TypeOK == TypeOK /\ UNCHANGED <<seq, orig, worklist, pc>>

\* The full invariant used by the toolbox: domain partitioning, permutation
\* preservation, and the sortedness relation between intervals.
Inv ==
  /\ \A i \in Domain : seq[i] \in Values
  /\ seq = Permutation(orig, [i \in Domain |-> i])
  /\ \A i, j \in Domain : (i <= j) => (seq[i] <= seq[j])

Termination ==
  (pc = "choice") ~> (pc = "done")

\* The .cfg file replaces the standard Sequences.Seq with a bounded version.
\* This operator is intentionally not declared here; the .cfg binds the name.
LimitedSeq(s) == s

=============================================================================