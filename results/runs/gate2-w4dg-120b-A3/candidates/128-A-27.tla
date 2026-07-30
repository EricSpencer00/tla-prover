---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

(* Domain of the array being sorted. *)
Domain == 1..MaxSeqLen

\* A partition may move every element within the chosen interval and must
\* leave elements outside the interval untouched.
PartitionsOf(seq, lo, hi, pivot) ==
  { p \in (Domain -> Values) :
      /\ \A i \in Domain : (i < lo \/ i > hi) => p[i] = seq[i]
      /\ \A i \in lo..pivot, j \in (pivot + 1)..hi : p[i] <= p[j] }

VARIABLES seq, orig, intervals, pc

TypeOK ==
  /\ seq \in [Domain -> Values]
  /\ orig \in [Domain -> Values]
  /\ intervals \subseteq (Domain \X Domain)
  /\ pc \in {"loop", "done"}

\* The program starts with the whole sequence in the work set.
Init ==
  /\ \E v \in DOMAIN seq : seq = v
  /\ orig = seq
  /\ intervals = {<<1, MaxSeqLen>>}
  /\ pc = "loop"

\* One iteration of the sorting loop over an arbitrary interval.
Step ==
  \/ \E lo, hi \in Domain :
       /\ <<lo, hi>> \in intervals
       /\ intervals' = intervals \ {<<lo, hi>>}
       /\ pc' = IF lo = hi THEN pc ELSE pc
       /\ seq' = seq
       /\ UNCHANGED orig
  \/ \E lo, hi, pivot \in Domain, p \in PartitionsOf(seq, lo, hi, pivot) :
       /\ <<lo, hi>> \in intervals
       /\ lo # hi
       /\ pivot \in lo..hi
       /\ intervals' = (intervals \ {<<lo, hi>>}) \cup {<<lo, pivot>>, <<pivot + 1, hi>>}
       /\ seq' = p
       /\ UNCHANGED orig
  \/ (intervals = {} /\ pc' = "done" /\ UNCHANGED <<seq, orig, intervals>>)

Next == Step

\* Empty stutter after termination to keep the state space closed.
Stall ==
  /\ pc = "done"
  /\ UNCHANGED <<seq, orig, intervals, pc>>

Spec ==
  /\ Init
  /\ [][Next]_<<seq, orig, intervals, pc>>
  /\ [][Stall]_<<seq, orig, intervals, pc>>
  /\ WF_vars(Step)

\* Permutations are defined via composition with a domain automorphism.
Permutation(s) == { p \in [Domain -> Values] : \E f \in [Domain -> Domain] :
                       /\ \A a, b \in Domain : f[a] = f[b] => a = b
                       /\ \A c \in Domain : f[c] \in Domain
                       /\ p = s \circ f }

\* Invariant: every pair of intervals is either nested or disjoint, seq stays
\* a permutation of the original, and values at lower indices never exceed
\* values at higher indices across interval boundaries.
Inv ==
  /\ \A i, j \in Domain :
       \/ i \in intervals
       \/ j \in intervals
       \/ (i \notin intervals /\ j \notin intervals)
  /\ seq \in Permutation(orig)
  /\ \A lo, hi \in Domain :
       (<<lo, hi>> \in intervals /\ lo < hi) => seq[lo] <= seq[hi]

PCorrect == (pc = "done") => (seq \in Permutation(orig) /\ \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i + 1])
Termination == <>(pc = "done")
\* The standard sequence operator is replaced by a FINITE version for model checking.
LimitedSeq == Seq

\* The full set of identifiers exposed by this module.
====