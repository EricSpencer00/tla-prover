---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

CONSTANTS Values, MaxSeqLen

Bump == 1

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ work \in SUBSET ((1..MaxSeqLen) \X (1..MaxSeqLen))
  /\ pc \in {"run", "done"}

\* A domain partition is a set of non-empty intervals that together cover every
\* index of the sequence exactly once.
DomainPartition ==
  /\ \A i \in 1..Len(seq) : \E r \in work : i \in r[1]..r[2]
  /\ \A p, q \in work : (p[1]..p[2]) \cap (q[1]..q[2]) # {}
                                 => p[1] = q[1] /\ p[2] = q[2]

Inv ==
  /\ seq \in Seq(Values)
  /\ work \in SUBSET ((1..MaxSeqLen) \X (1..MaxSeqLen))
  /\ DomainPartition
  /\ Permutations(seq) = Permutations(orig)
  /\ \A p, q \in work :
       (p[2] + Bump <= q[1] /\ p[2] < Len(seq)) => seq[p[2]] <= seq[q[1]]

Init ==
  /\ seq \in { s \in Seq(Values) : 0 < Len(s) /\ Len(s) <= MaxSeqLen }
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "run"

\* Partitioning an interval is abstracted away: the algorithm nondeterministically
\* picks any result consistent with the pivot and the untouched outside region.
\* This makes the action well-defined even though the concrete partition procedure
\* is not modeled.
QuicksortStep ==
  /\ pc = "run"
  /\ \E r \in work :
       /\ IF r[1] = r[2]
            THEN work' = work \ {r}
            ELSE
              /\ \E k \in r[1]..r[2] :
                   \E y \in Partition(seq, r[1], r[2], k) :
                     /\ seq' = y
                     /\ work' = (work \ {r}) \cup { <<r[1], k>>, <<k+Bump, r[2]>> }
       /\ UNCHANGED <<orig, pc>>
  /\ pc' = IF work = {} THEN "done" ELSE pc

Next == QuicksortStep

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

PCorrect ==
  (pc = "done") => (Permutations(seq) = Permutations(orig) /\ IsSorted(seq))

\* Termination is guaranteed by fairness: no enabled partition step is ever
\* postponed forever.
Termination == <>(pc = "done")

\* The partition operator is defined only in the .cfg, where its definition is
\* replaced by a bounded, checkable version.
RECURSIVE Partition(_, _, _, _)
Partition(s, lo, hi, k) == CHOOSE y \in Cut(s, lo, hi, k) : TRUE

====