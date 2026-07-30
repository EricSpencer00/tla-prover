---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen, Seq

Intervals == [lo: 1 .. MaxSeqLen, hi: 1 .. MaxSeqLen]
Covered == { x \in 1 .. MaxSeqLen :
                \E a \in [lo : 1 .. MaxSeqLen, hi : 1 .. MaxSeqLen] : x \in a.lo .. a.hi }

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

Init ==
  /\ seq \in {s \in Seq : Len(s) >= 1}
  /\ orig = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "main"

DomPart(seq) ==
  { k \in 1 .. Len(seq) : \E i \in 1 .. Len(seq) : seq[i] = seq[k] }

Perm(seq1, seq2) ==
  \E g \in [1 .. Len(seq1) -> 1 .. Len(seq1)] :
    /\ \A i \in 1 .. Len(seq1) : seq1[g[i]] = seq2[i]
    /\ \A i \in 1 .. Len(seq1) : g[i] \in DomPart(seq1)

Partings(seq, a, p) ==
  { t \in Seq :
      /\ Len(t) = Len(seq)
      /\ \A i \in 1 .. Len(seq) : (i < a.lo \/ i > a.hi) => t[i] = seq[i]
      /\ \A i \in a.lo .. p : \A j \in p + 1 .. a.hi : t[i] <= t[j] }

Lower(a, p) == [lo |-> a.lo, hi |-> p]
Upper(a, p) == [lo |-> p + 1, hi |-> a.hi]

Step ==
  \/ \E a \in work :
       /\ work' = work \ {a}
       /\ \/ /\ a.lo = a.hi
             /\ UNCHANGED <<seq, orig>>
         \/ \E p \in a.lo .. a.hi :
              /\ seq' \in Partings(seq, a, p)
              /\ work' = work \cup {Lower(a, p), Upper(a, p)}
       /\ UNCHANGED orig
  \/ /\ work = {}
       /\ pc' = "done"
       /\ UNCHANGED <<seq, orig, work>>

Next == Step
Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

PCorrect ==
  (pc = "done") => (seq = orig \cup> seq /\ \A i \in 1 .. Len(seq) - 1 : seq[i] <= seq[i + 1])

TypeOK ==
  /\ seq \in Seq
  /\ orig \in Seq
  /\ work \subseteq Intervals
  /\ pc \in {"main", "done"}

SortedWithin(a, seq) ==
  \A i, j \in a.lo .. a.hi : i <= j => seq[i] <= seq[j]

Inv ==
  /\ \A i \in 1 .. Len(seq) : i \in Covered
  /\ Perm(seq, orig)
  /\ \A a \in work : SortedWithin(a, seq)

Termination == (pc = "done")

====