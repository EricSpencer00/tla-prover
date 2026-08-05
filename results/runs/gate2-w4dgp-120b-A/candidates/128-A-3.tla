---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

VARIABLES seq, original, intervals, pc
vars == <<seq, original, intervals, pc>>

Work == UNION {{i} : i \in 1..MaxSeqLen}
Intervals == UNION {SUBSET (1..n) : n \in 1..MaxSeqLen}

PartialSeq(n) == {s \in Seq(Values) : Len(s) = n}
SeqOf(n) == {s \in Seq(Values) : Len(s) <= n}
Domain(s) == 1..Len(s)

\* A permutation of a finite sequence is defined as a composition with an
\* automorphism of its domain; re-uses the standard Seq operator as its
\* meaning -- the .cfg replaces Seq with a bounded variant.
Permutation(s, t) == \E f \in [Domain(s) -> Domain(s)] : (\A i \in Domain(s) : f[i] = f[j] => i = j) /\ (\A i \in Domain(s) : t[i] = s[f[i]])

TypeOK ==
  /\ seq \in SeqOf(MaxSeqLen) /\ seq # <<>>
  /\ original \in SeqOf(MaxSeqLen) /\ original # <<>>
  /\ intervals \subseteq Intervals /\ intervals /= {}

\* p is a valid partition of s on interval I: s is unchanged outside I and
\* every element at or below the pivot is <= every element above it.
ValidPartition(s, p, I, pivot) ==
  /\ \A i \in Domain(s) \ I : p[i] = s[i]
  /\ \A i \in I : \A j \in I : (i <= pivot /\ j > pivot) => p[i] <= p[j]

Init ==
  /\ \E s \in SeqOf(MaxSeqLen) : s # <<>> /\ seq = s /\ original = s
  /\ intervals = {Domain(s)} /\ pc = "running"

Step ==
  /\ pc = "running"
  /\ intervals # {}
  /\ \E I \in intervals :
       /\ intervals' = intervals \ {I}
       /\ IF I = {i} THEN intervals' = intervals \ {I}
          ELSE
            /\ \E pivot \in I :
                 /\ \E p \in {t \in Seq(Values) : ValidPartition(seq, t, I, pivot)} :
                      /\ seq' = p
                      /\ LET lo == {i \in I : i <= pivot} /\ hi == {i \in I : i > pivot} IN
                         intervals' = intervals \cup (IF lo = {} THEN {} ELSE {lo}) \cup (IF hi = {} THEN {} ELSE {hi})
  /\ pc' = IF intervals' = {} THEN "done" ELSE "running"

Stall == pc = "done" /\ pc' = "done" /\ UNCHANGED <<seq, original, intervals>>

Next == Step \/ Stall

\* Domains are always a set of intervals that partition a prefix of the
\* domain of the original sequence -- their pairwise intersection is empty.
DomainPartitions ==
  /\ \A I1, I2 \in intervals : I1 \cap I2 = {} \/ I1 = I2
  /\ (\A i \in Domain(seq) : \E I \in intervals : i \in I)

Inv == DomainPartitions /\ Permutation(original, seq) /\ (\A i \in Domain(seq) : \A j \in Domain(seq) : (i < j) => seq[i] <= seq[j])

PCorrect ==
  pc = "done" => (\A i \in Domain(seq) : \A j \in Domain(seq) : (i < j) => seq[i] <= seq[j])

Spec == Init /\ [][Next]_vars

Termination == WF_vars(Step)

====