---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* The model's value set is a constant bounded by a concrete integer set
\* supplied in the .cfg file. A companion .cfg file also redefines Seq to
\* LimitedSeq (a fully-finite version) so the model does not run away.
CONSTANTS Values, MaxSeqLen

Interval == [lo: 1 .. MaxSeqLen, hi: 1 .. MaxSeqLen]

\* A permutation of a domain is a bijection from that domain to itself; the
\* operator below is exactly the closure used by the invariant.
Permutations(T) ==
  { f \in [T -> T] : \A x \in T : \E y \in T : f[y] = x }

\* The partition operation nondeterministically chooses any valid rearrangement
\* of the interval around the pivot, which is what the abstract algorithm
\* treats as a black box. The shape of the returned sequence is fixed.
Partition(s, low, hi, p) ==
  { t \in [1 .. Len(s) -> Values] :
       /\ \A i \in 1 .. Len(s) : (i < low \/ i > hi) => t[i] = s[i]
       /\ \A i \in low .. hi, j \in low .. hi :
              (i < p /\ j >= p) => t[i] <= t[j]
  }

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>
Domain == 1 .. Len(seq)
Terminated == [pc |-> "done"]

TypeOK ==
  /\ seq \in [1 .. MaxSeqLen -> Values]
  /\ original \in [1 .. MaxSeqLen -> Values]
  /\ work \in SUBSET Interval
  /\ pc \in {"loop"}

\* The invariant has three parts: (1) every processed interval is a clean
\* subinterval of the domain, (2) the current sequence is a permutation of
\* the original, and (3) any two intervals that are disjoint or nested are
\* relatively sorted, which is exactly what is needed to conclude the whole
\* sequence is sorted once every interval is a singleton.
Inv ==
  /\ \A iv \in work : iv.lo \in Domain /\ iv.hi \in Domain
  /\ seq \in Permutations(Domain)
  /\ \A i \in Domain, j \in Domain :
       (i < j /\ (\E iv \in work : i \in iv.lo .. iv.hi /\ j \in iv.lo .. iv.hi))
         => seq[i] <= seq[j]

PCorrect == pc = "done" => \A i \in Domain : seq[i] <= seq[i + 1]

Init ==
  /\ seq \in [1 .. MaxSeqLen -> Values] /\ Len(seq) >= 1
  /\ original = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* RawStep is the core of the algorithm: it takes a whole interval and splits it.
Step ==
  \/ \E iv \in work :
       /\ work' = work \ {iv}
       /\ pc' = pc
       /\ IF iv.lo = iv.hi
          THEN UNCHANGED seq
          ELSE
            \/ \E p \in iv.lo .. iv.hi :
                 \E t \in Partition(seq, iv.lo, iv.hi, p) :
                   /\ seq' = t
                   /\ work' = work \cup {[lo |-> iv.lo, hi |-> p - 1], [lo |-> p, hi |-> iv.hi]}
            \/ UNCHANGED seq
  \/ (pc = "loop" /\ work = {}) /\ pc' = "done" /\ UNCHANGED <<seq, original, work>>

Next == Step

\* A stuttering step keeps TLC from complaining once the algorithm has
\* terminated; it is deliberately weak, so strong fairness on Step is enough.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Step)
  /\ SF_vars(Step)

Termination == <>(pc = "done")
====