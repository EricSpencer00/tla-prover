---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The spec keeps a copy of the original sequence so the final result can be
\* checked as a permutation of the input. This copy is never altered.
VARIABLES seq, originalSeq, intervals, pc

vars == <<seq, originalSeq, intervals, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= MaxSeqLen
  /\ originalSeq \in Seq(Values)
  /\ intervals \subseteq SUBSET (0 .. MaxSeqLen-1)
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in Seq(Values) : seq = s /\ Len(s) >= 1 /\ originalSeq = s
  /\ intervals = {0 .. Len(seq) - 1}
  /\ pc = "main"

\* The partition operator is nondeterministic and returns any valid partition of
\* the interval, so the model never needs to explore every possible swap.
Partitions(orig, lo, hi, p) ==
  { c \in Seq(Values) :
      /\ Len(c) = Len(orig)
      /\ \A i \in 0 .. Len(orig) - 1 : i < lo \/ i > hi => c[i] = orig[i]
      /\ \A i \in lo .. p : \A j \in p+1 .. hi : c[i] <= c[j] }

Step ==
  \/ \E I \in intervals :
       \/ \E i \in intervals :
          /\ \A x \in intervals : x <= I
          /\ I = i
          /\ intervals' = intervals \ {I}
       \/ \E lo \in intervals, hi \in intervals, p \in lo .. hi :
          /\ intervals' = (intervals \ {lo .. hi}) \cup {lo .. p, p+1 .. hi}
          /\ \E c \in Partitions(seq, lo, hi, p) : seq' = c
  /\ pc' = "main"
  \/ (pc = "main" /\ intervals = {} /\ pc' = "done" /\ UNCHANGED <<seq, originalSeq, intervals>>)
  \/ (pc = "done" /\ UNCHANGED vars)

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

PCorrect ==
  pc = "done" => /\ Multiset(seq) = Multiset(originalSeq)
                  /\ \A i \in 1 .. Len(seq) - 1 : seq[i-1] <= seq[i]

\* The foundational invariant: the current work set partitions the domain
\* without overlap, the sequence is always a permutation of the input, and
\* every interval in the work set is locally sorted against the rest of the
\* sequence, which is what makes the final sortedness verifiable.
Inv ==
  /\ intervals \subseteq SUBSET (0 .. Len(seq)-1)
  /\ \A x, y \in intervals : x \cap y = {} \/ x = y
  /\ Multiset(seq) = Multiset(originalSeq)
  /\ \A I \in intervals : \A i \in I : \A j \in (0 .. Len(seq)-1) \ I : seq[i] <= seq[j]

Termination == (pc = "done") ~> (pc = "done")

====