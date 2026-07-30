---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A bounded version of the unbounded Sequences operator, needed for model
\* checking so the model stays finite.  The name Seq is never declared here.
LimitedSeq(T) == { s \in Seq(T) : Len(s) <= MaxSeqLen }

VARIABLES seq, origrange, work, pc

vars == <<seq, origrange, work, pc>>

Range(f) == { f[i] : i \in DOMAIN f }

\* A permutation of T is any total function from DOMAIN T to the range of T.
Permutation(T) ==
  { f \in [DOMAIN T -> Range(T)] : \E g \in DOMAIN~T : f = T \circ g }

\* The partition operator: inside the interval it is a permutation of the
\* original values; outside it the sequence is unchanged; and the pivot
\* enforces relative ordering across the split point.
Part(s, low, high, pivot) ==
  { t \in Permutation(s) :
      /\ \A i \in DOMAIN s : (i < low \/ i > high) => t[i] = s[i]
      /\ \A i \in low..pivot, j \in (pivot + 1)..high : t[i] <= t[j] }

TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ origrange \in LimitedSeq(Values)
  /\ work \subseteq [l : 1..MaxSeqLen, h : 1..MaxSeqLen]
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in LimitedSeq(Values) : seq = s /\ origrange = s
  /\ work = { [l |-> 1, h |-> Len(seq)] }
  /\ pc = "main"

\* Weak fairness below is what makes the work set shrink.
Step ==
  \/ \E iv \in work :
       /\ iv.l = iv.h
       /\ work' = work \ { iv }
       /\ UNCHANGED <<seq, origrange>>
     \/ \E iv \in work, pivot \in iv.l..iv.h :
          /\ LET low == iv.l
                 high == iv.h
                 newseq \in Part(seq, low, high, pivot)
                 left  == [l |-> low, h |-> pivot]
                 right == [l |-> pivot + 1, h |-> high]
          IN /\ seq' = newseq
             /\ work' = (work \ { iv }) \cup { left, right }
       /\ UNCHANGED origrange
  \/ \E iv \in work :
       /\ work' = work \ { iv }
       /\ UNCHANGED <<seq, origrange>>
  \/ (work = {} /\ pc = "main") /\ pc' = "done"
  \/ (pc = "done") /\ UNCHANGED vars

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Psorted ==
  \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* The partial proof below is TLAPS-checked, not model-checked.
PCorrect == pc = "done" => (Psorted /\ seq \in Permutation(origrange))

DomainPartition ==
  \A i \in DOMAIN seq : \E iv \in work : i \in iv.l..iv.h

PermutationPreservation ==
  \A i \in DOMAIN seq : seq[i] \in Range(origrange)

RelativeSortedness ==
  \A iv \in work :
    \A i, j \in iv.l..iv.h : i < j => seq[i] <= seq[j]

Inv == DomainPartition /\ PermutationPreservation /\ RelativeSortedness

Termination == pc = "done"

====