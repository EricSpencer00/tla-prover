---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

\* The .cfg file redefines Seq as a finite version for model checking and
\* asks for an operator on the right side only; the name itself is not
\* declared here and must not be redefined in this module.
LimitedSeq == (o) :> IF o \in Nat /\ o <= MaxSeqLen THEN Len(Seq(o)) ELSE 0

CONSTANTS Values, MaxSeqLen

Intervals == UNION {[i, j] : i \in 1..MaxSeqLen, j \in 1..MaxSeqLen}

VARIABLES seq, orig, workset, pc
vars == <<seq, orig, workset, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ workset \subseteq Intervals
  /\ pc \in {"loop", "done"}

\* Permutations are modeled via automorphisms of the index domain.
RECURSIVE Permutes(_)
Permutes(S) ==
  IF S = {} THEN {<<>>}
  ELSE UNION {AppendSeq(s, e) : s \in Permutes(S \ {e}), e \in S}

\* A partition may reorder freely inside and outside the chosen interval, but
\* must respect the pivot ordering that a valid Quicksort partition enforces.
PartitionOf(e, i, k, pivot) ==
  { e' \in Permutes(e) :
      /\ \A n \in 1..Len(e) : e'[n] = e[n]
      /\ \A a, b \in i..k : (a <= pivot /\ b > pivot) => e'[a] <= e'[b] }

Init ==
  /\ \E s \in Permutes(Values) : seq = s
  /\ orig = seq
  /\ workset = {[1, Len(seq)]}
  /\ pc = "loop"

\* The single step of the algorithm: partition an interval or retire a singleton.
QuicksortStep ==
  /\ pc = "loop"
  /\ \E i, k \in 1..Len(seq) :
       /\ [i, k] \in workset
       /\ IF i = k
          THEN workset' = workset \ {[i, k]}
          ELSE \E pivot \in i..k :
                 /\ \E e' \in PartitionOf(seq, i, k, pivot) : seq' = e'
                 /\ workset' = (workset \ {[i, k]}) \cup {[i, pivot], [pivot + 1, k]}
  /\ pc' = IF (workset \ {[i, k]}) \cup ({[i, pivot], [pivot + 1, k]} \ {[i, k]}) = {}
            THEN "done"
            ELSE "loop"
  /\ orig' = orig

Next == QuicksortStep \/ (pc = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep)

\* The invariant is a conjunction of three facts; splitting it keeps each
\* conjoinable in the shape that TLC can check.
Inv ==
  /\ \A i, k \in 1..Len(seq) :
       /\ [i, k] \in workset => i <= k
       /\ i > 1 => seq[i-1] <= seq[i]
  /\ \A i \in 1..Len(seq) : seq[i] \in Values
  /\ \A i, j \in 1..Len(seq) :
       (i # j /\ seq[i] = seq[j]) => seq'[[j]] = seq'[[i]]

PCorrect ==
  /\ (pc = "done" => \A i \in 1..Len(seq) : seq[i] = orig[i])
  /\ (pc = "done" => \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1])

Termination == <>(pc = "done")
====