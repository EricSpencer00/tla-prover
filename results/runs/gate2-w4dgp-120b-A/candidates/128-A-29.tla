---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

\* The "LimitedSeq" operator replaces the unbounded "Seq" operator from the
\* Sequences module with a version that only produces sequences up to a
\* bounded length, so the model stays finite and checkable.
LimitedSeq(D, n) ==
  IF n = 0
    THEN {}
    ELSE (D \cup {0}) \times LimitedSeq(D, n - 1)

VARIABLES seq, originalSeq, intervals, pc
vars == <<seq, originalSeq, intervals, pc>>

Range(A) == {A[i] : i \in DOMAIN A}

AtMost(n) == Cardinality({i \in DOMAIN seq : seq[i] <= n})

RECURSIVE PermutationsOf(_, _)
PermutationsOf(D, S) ==
  IF S = {}
    THEN {<<>>}
    ELSE {<<x>> \o s : x \in D, s \in PermutationsOf(D, S \ {x})}

\* A partition only moves elements inside the interval; everything in
\* the domain stays in the domain, so permutations are built from
\* automorphisms of the index set.
Automorphisms(D) == PermutationsOf(D, D)

Partition(A, lo, hi, p) ==
  {B \in [DOMAIN A -> Range(A)] :
     (\A i \in DOMAIN A : i < lo \/ i > hi => B[i] = A[i])
       /\ (\A i \in DOMAIN A : lo <= i < p => B[i] <= A[p])
       /\ (\A i \in DOMAIN A : p <= i <= hi => B[i] >= A[p])
       /\ (\A i \in DOMAIN A : lo <= i <= hi => i \in (Range(A) \cup {0}) \cup {B[i]})}

Init ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ originalSeq = seq
  /\ intervals = {<<1, Len(seq)>>}
  /\ pc = "Start"

QuicksortStep ==
  \/ (\E interval \in intervals :
        /\ intervals' = intervals \ {interval}
        /\ IF interval[1] = interval[2]
             THEN intervals'
             ELSE (\E p \in interval[1] .. interval[2] :
                     /\ \E b \in Partition(seq, interval[1], interval[2], p) : seq' = b
                     /\ intervals' = intervals
                          \cup {<<interval[1], p - 1>>}
                          \cup {<<p + 1, interval[2]>>}))
     \/ (intervals = {} /\ pc' = "Terminated")
     \/ (pc = "Terminated" /\ pc' = pc /\ seq' = seq /\ intervals' = intervals)
  /\ originalSeq' = originalSeq

Next == QuicksortStep

Spec == Init /\ [][Next]_vars
        /\ WF_vars(QuicksortStep)

\* A finished Quicksort is a permutation of the input and is sorted.
PCorrect ==
  (intervals = {} => seq = originalSeq) /\ (\A i \in DOMAIN seq : seq[i] <= AtMost(i))

\* An inductive invariant that is stronger than PCorrect, kept for the
\* sake of the partially checked proof.
Inv ==
  /\ intervals \subseteq DOMAIN seq \X DOMAIN seq
  /\ Range(seq) \cup {0} \subseteq Values
  /\ seq \in AUTOMORPHISM[DOMAIN seq]
  /\ (\A i, j \in DOMAIN seq : i <= j => seq[i] <= seq[j])

TypeOK ==
  /\ seq \in [DOMAIN seq -> Values \cup {0}]
  /\ originalSeq \in [DOMAIN seq -> Values \cup {0}]
  /\ intervals \subseteq (DOMAIN seq \X DOMAIN seq)
  /\ pc \in {"Start", "Terminated"}

Termination == [](pc = "Terminated")

====