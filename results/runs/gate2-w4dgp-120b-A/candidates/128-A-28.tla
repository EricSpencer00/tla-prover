---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

CONSTANTS Values, MaxSeqLen

\* The count of indices of a sequence of length n (1-indexed in a sequence)
DOMAIN == MaxSeqLen

\* Redefine Seq as a version that is guaranteed finite for model checking. It
\* has the same semantics as Sequences!Seq -- only the bound differs.
LimitedSeq(T) == { s \in [1..MaxSeqLen -> T] : Len(s) <= MaxSeqLen }

\* A partition of s over interval i around pivot p is any permutation of s that
\* keeps the outside of i unchanged, and respects the pivot: everything at or
\* below p is no greater than everything above it.
Partition(s, i, p) ==
  { t \in Automorphism(s) :
      \A k \in 1..Len(s) :
        (k < i.m \/ k > i.M) => t[k] = s[k]
      /\ \A k \in i.m..p, l \in (p+1)..i.M : t[k] <= t[l] }

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq [m : 1..MaxSeqLen, M : 1..MaxSeqLen]
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in LimitedSeq(Values) : s # <<>> /\ seq = s /\ orig = s
  /\ work = {[m |-> 1, M |-> Len(s)]}
  /\ pc = "loop"

\* A partition step either collapses a singleton interval, or chooses a pivot
\* and a valid partition outcome, then subdivides the interval.
Step ==
  /\ pc = "loop" /\ work # {}
  /\ \E i \in work :
       LET rest == work \ {i} IN
       IF i.m = i.M
         THEN /\ work' = rest
              /\ UNCHANGED <<seq, orig>>
         ELSE /\ \E p \in i.m..i.M :
               /\ \E s2 \in Partition(seq, i, p) : seq' = s2
               /\ work' = rest \cup {[m |-> i.m, M |-> p], [m |-> p+1, M |-> i.M]}
         /\ UNCHANGED orig
  /\ UNCHANGED pc

Done == pc = "loop" /\ work = {} /\ pc' = "done" /\ UNCHANGED <<seq, orig, work>>

Stall == pc = "done" /\ UNCHANGED vars

Next == Step \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Done)

\* The algorithm only moves elements inside the interval it is currently
\* working on, so each interval's interior is a permutation of the input.
PerIntervalPerm ==
  \A i \in work :
    \A x \in DOMAIN :
      (i.m <= x /\ x <= i.M) =>
        \E y \in DOMAIN :
          (i.m <= y /\ y <= i.M) /\ seq[x] = orig[y]

\* Relative sortedness: every element of a lower interval is no greater than
\* every element of a strictly higher interval.
RelativeOrder ==
  \A i, j \in work :
    (i.M < j.m) =>
      \A x \in DOMAIN, y \in DOMAIN :
        (i.m <= x /\ x <= i.M /\ j.m <= y /\ y <= j.M) => seq[x] <= seq[y]

\* The whole point of Quicksort: a terminated run is a sorted permutation of
\* the input.
PCorrect == (pc = "done") => (Permutation(seq, orig) /\ Sorted(seq))

Inv == PerIntervalPerm /\ RelativeOrder

Termination == <> (pc = "done")

====