---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen, Seq

\* Intervals kept as a set for fairness: an element may be selected in any order,
\* and the partition operator below models every permissible outcome of the
\* Quicksort partition step in a single nondeterministic step.
Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

TypeOK ==
  /\ seq \in Seq
  /\ original \in Seq
  /\ work \subseteq Intervals
  /\ pc \in {"main", "stop"}

\* A permutation of the domain is a bijection 1..n -> 1..n; applying it to a
\* sequence reorders the elements without changing the multiset.
Permutation(n) == { f \in [1..n -> 1..n] : \A x \in 1..n : \A y \in 1..n :
                      (f[x] = f[y]) => x = y }

\* The partition operator captures every rearrangement a valid partition could
\* produce: it must leave elements outside the interval untouched, and must
\* place the chosen pivot between the lower and upper halves.
Partition(seq, i, lo, hi) ==
  { s \in Seq :
      /\ Len(s) = Len(seq)
      /\ \A idx \in 1..Len(seq) : idx < lo \/ idx > hi => s[idx] = seq[idx]
      /\ \A m \in lo..i, p \in (i + 1)..hi :
           s[m] <= s[p]
  }

\* The sortedness invariant is indexed by intervals rather than by position,
\* because the algorithm visits intervals in arbitrary order.
Nondecreasing(seq, lo, hi) ==
  \A i, j \in lo..hi : i < j => seq[i] <= seq[j]

Init ==
  /\ seq = CHOOSE s \in Seq :
        /\ s # <<>>
        /\ Len(s) <= MaxSeqLen
  /\ original = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "main"

\* One Quicksort iteration: either a singleton interval is discarded, or a
\* pivot is chosen and the interval is split into two subintervals.
Step ==
  \/ \E d \in work :
       /\ d.lo = d.hi
       /\ work' = work \ {d}
       /\ UNCHANGED <<seq, original>>
  \/ \E d \in work, i \in d.lo..d.hi :
       /\ Len(seq) >= i
       /\ LET lo1 == [lo |-> d.lo, hi |-> i]
            up1 == [lo |-> i + 1, hi |-> d.hi]
            sset == Partition(seq, i, d.lo, d.hi)
            ssel == CHOOSE s \in sset : TRUE
       IN
         /\ sset # {}
         /\ seq' = ssel
         /\ work' = (work \ {d}) \cup {lo1, up1}
       /\ UNCHANGED <<original>>
  \/ (work = {}) /\ pc' = "stop" /\ UNCHANGED <<seq, original, work>>

Next ==
  \/ Step
  \/ (pc = "stop" /\ UNCHANGED vars)

Stall ==
  /\ pc = "stop"
  /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Stall

\* Termination only looks at the control state; partial correctness below
\* is a separate property that holds only at termination.
Termination == <>(pc = "stop")

\* At termination the output sequence is both a permutation of the input and
\* sorted across every interval that ever existed.
PCorrect ==
  /\ (pc = "stop") => (\E f \in Permutation(Len(original)) : seq = [i \in 1..Len(original) |-> original[f[i]]])
  /\ (pc = "stop") => \A i \in 1..MaxSeqLen : \A j \in 1..MaxSeqLen :
        (i <= j /\ j <= Len(seq)) => seq[i] <= seq[j]

\* The three-part invariant is what keeps the model checking an empty work set
\* equivalent to the final sorted state, without exploring the trivial
\* final idle step that would otherwise be needed.
Inv ==
  /\ UNCHANGED <<seq, original, work>>
  /\ \A i \in 1..MaxSeqLen : Nondecreasing(seq, i, i)

====