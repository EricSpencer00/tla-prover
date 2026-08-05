---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

(*======================================================================*)
(* This module implements an abstract version of the Quicksort sorting    *)
(* algorithm.  It is one of the examples from Section 7.3 of Leslie        *)
(* Lamport's "Proving Safety Properties": the QuickSort procedure is      *)
(* defined in a PlusCal block below, and the generated state machine      *)
(* carries a partial-correctness theorem stating that termination         *)
(* implies a sorted permutation of the original sequence.                 *)
(*                                                                      *)
(* The partition step is abstracted: given an interval and a pivot         *)
(* position, the algorithm nondeterministically chooses any sequence that  *)
(* is a valid partition of the current sequence over that interval.        *)
(*                                                                      *)
(* The action set is deliberately tiny: one transition that folds the     *)
(* entire loop body, and one terminating transition.  The invariant tracks *)
(* the partitioning discipline in terms of a domain partition (the set   *)
(* of intervals currently being processed) and a permutation invariant,    *)
(* plus a pairwise-sortedness condition between intervals.                *)
(*======================================================================*)

CONSTANTS Values, MaxSeqLen

\* A finite bound on the sequence length for model checking; the algebraic
\* proof in the .cfg file works with unbounded sequences.
SeqBound == MaxSeqLen

VARIABLES seq, original, workset, pc
vars == <<seq, original, workset, pc>>

Domain == 1 .. Len(seq)

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= SeqBound
  /\ original \in Seq(Values)
  /\ workset \in SUBSET (Domain \X Domain)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in SeqBounded(Values, SeqBound) : seq = s /\ original = s
  /\ workset = {<<1, Len(s)>>}
  /\ pc = "loop"

\* Partition relation: for the chosen interval [a..b] and pivot p, all
\* sequences that keep elements outside the interval untouched while
\* placing everything at or below the pivot no greater than everything
\* above it are admitted.
\* The last clause keeps the algorithm realistic by forbidding a
\* partition that moves elements outside the chosen interval.
Partition(a, b, p) ==
  { s \in SeqBounded(Values, SeqBound) :
      /\ Len(s) = Len(seq)
      /\ s[a - 1] = seq[a - 1]
      /\ s[b] = seq[b]
      /\ \A i \in a..p : \A j \in (p+1)..b : s[i] <= s[j]
      /\ \A k \in Domain \ (a..b) : s[k] = seq[k] }

SortStep ==
  /\ pc = "loop"
  /\ workset # {}
  /\ \E a, b \in Domain :
       /\ <<a, b>> \in workset
       /\ IF a = b
          THEN workset' = workset \ {<<a, b>>}
          ELSE
            /\ \E p \in a..b :
                 /\ \E s \in Partition(a, b, p) :
                      /\ seq' = s
                      /\ workset' = (workset \ {<<a, b>>})
                                   \cup {<<a, p>>, <<p+1, b>>}
            /\ UNCHANGED original
  /\ pc' = pc

Terminate ==
  /\ pc = "loop"
  /\ workset = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, workset>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == SortStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(SortStep) /\ WF_vars(Terminate)

\* A domain partition is a set of intervals whose domains form a partition
\* of the whole index set.
DomainPartition(P) ==
  /\ \E f \in [P -> [Domain -> BOOLEAN]] :
       /\ \A r \in P : \A i \in r[1]..r[2] : f[r][i]
       /\ \A r, q \in P : r # q => \A i \in Domain : ~(f[r][i] /\ f[q][i])
       /\ \A i \in Domain : \E r \in P : f[r][i]

\* A sorted partition is a domain partition where every pair of intervals
\* respects the non-decreasing order: the last element of a lower interval
\* is no greater than the first element of a higher interval.
SortedPartition(P) ==
  DomainPartition(P) /\ \A r, q \in P :
    (r[1] >= q[2] /\ ~ (r[2] = q[2])) => seq[q[2]] <= seq[r[1]]

\* The partial-correctness theorem: termination implies the output is a
\* sorted permutation of the original sequence.
PartialCorrectness ==
  (pc = "done") => (seq = original \circledast Permutations(Domain) /\ SortedPartition(workset))

Inv == (\A i, j \in Domain : seq[i] <= seq[j]) /\ SortedPartition(workset)

Termination == <>(pc = "done")

=============================================================================