---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* FiniteSequences.Seq built from a primitive recursion; the standard
\* Sequences.Seq operator is not checkable because it admits infinite
\* sequences, so this bounded version is what the .cfg file substitutes.
LimitedSeq == [n \in Nat |-> { f \in [1..n -> Values] : \A i \in 1..n : f[i] \in Values }]

Range(s) == {s[i] : i \in 1..Len(s)}

\* An interval of indices in the sequence (lower <= upper) -- the work set
\* is a set of such intervals, each of which is refined until it is a
\* singleton.
INTERVAL == [lower: 1..MaxSeqLen, upper: 1..MaxSeqLen]

VARIABLES seq, originalSeq, workSet, pc

vars == <<seq, originalSeq, workSet, pc>>

Bounded == Len(seq) <= MaxSeqLen

TypeOK ==
  /\ seq \in LimitedSeq[MaxSeqLen]
  /\ originalSeq \in LimitedSeq[MaxSeqLen]
  /\ workSet \subseteq INTERVAL
  /\ pc \in {"sorting", "done"}

Init ==
  /\ \E s \in LimitedSeq[MaxSeqLen] : s # <<>> /\ seq = s /\ originalSeq = s
  /\ workSet = {[lower |-> 1, upper |-> Len(seq)]}
  /\ pc = "sorting"

\* Any permutation of the domain that leaves elements outside the interval
\* alone and respects the partition ordering at the pivot index.
Partition(d, iv, k) ==
  {f \in [1..Len(seq) -> Values] :
     /\ \A i \in 1..Len(seq) : (i < iv.lower \/ i > iv.upper) => f[i] = seq[i]
     /\ \A i \in iv.lower..k : \A j \in k+1..iv.upper : f[i] <= f[j]}

Refine ==
  /\ pc = "sorting"
  /\ workSet # {}
  \/ \E iv \in workSet :
       /\ IF iv.lower = iv.upper
          THEN workSet' = workSet \ {iv}
          ELSE
            \E k \in iv.lower..iv.upper :
              /\ \E f \in Partition(seq, iv, k) : seq' = f
              /\ workSet' = (workSet \ {iv})
                               \cup {[lower |-> iv.lower, upper |-> k]}
                               \cup {[lower |-> k+1, upper |-> iv.upper]}
       /\ UNCHANGED <<originalSeq, pc>>

Terminate ==
  /\ pc = "sorting"
  /\ workSet = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, originalSeq, workSet>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Refine \/ Terminate \/ Stall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Refine)
  /\ SF_vars(Terminate)

\* The final sequence is a permutation of the input and is sorted.
PCorrect == pc = "done" => /\ Range(seq) = Range(originalSeq) /\ Len(seq > 0)
                        /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i+1]

\* Inductive shape: domain partition plus an ordered relation between
\* adjacent intervals that together imply the whole sequence is sorted.
Sorted(i) == \E j \in 1..MaxSeqLen : i <= j /\ \A k \in i..j : seq[k] <= seq[k+1]
DomainBound == Len(seq) <= MaxSeqLen
DomainPartition ==
  /\ Union({{i} : i \in 1..Len(seq)})
       = UNION({{i} : i \in 1..MaxSeqLen})
  /\ \A i \in 1..(MaxSeqLen - 1) : i \notin 1..Len(seq) => seq[i] <= seq[i+1]
Inv == /\ Bounded /\ DomainBound
       /\ DomainPartition /\ \A i \in 1..(MaxSeqLen - 1) : Sorted(i)

Termination == <>(pc = "done")

====