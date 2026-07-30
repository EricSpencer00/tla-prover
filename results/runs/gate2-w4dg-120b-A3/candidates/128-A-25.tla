---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Values, MaxSeqLen

\* An interval is a contiguous range of indices into the sequence.
Interval == [lo : 1 .. MaxSeqLen, hi : 1 .. MaxSeqLen]

VARIABLES seq, origSeq, work, pc

vars == << seq, origSeq, work, pc >>

\* The Partition operator is a constrained-relaxation of the true
\* partition step: it produces any permutation that respects the
\* sortedness invariant across one pivot boundary.
ValidPartition(s, t, iv, p) == /\ \A i \in 1 .. Len(s) : s[i] = t[i]
                            /\ \A i \in iv.lo .. p : \A j \in p + 1 .. iv.hi :
                                 t[i] <= t[j]

TypeOK ==
  /\ seq \in Seq(Values)
  /\ origSeq \in Seq(Values)
  /\ Len(origSeq) = Len(seq)
  /\ Len(seq) <= MaxSeqLen
  /\ work \subseteq Interval
  /\ pc \in {"loop", "done"}
  /\ work = {} => pc = "done"

Init ==
  /\ \E s \in SeqOf(Values, MaxSeqLen) :
        /\ s # << >>
        /\ seq' = s
        /\ origSeq' = s
  /\ work' = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc' = "loop"

PickInterval == { iv \in work : TRUE }

Next ==
  /\ \E iv \in PickInterval :
        /\ work' = (IF iv.lo = iv.hi THEN work \ {iv}
                    ELSE \E p \in iv.lo .. iv.hi :
                           /\ p > iv.lo
                           /\ p < iv.hi
                           /\ \E t \in Seq(Values) :
                                /\ ValidPartition(seq, t, iv, p)
                                /\ seq' = t
                           /\ work \ {iv} \cup {[lo |-> iv.lo, hi |-> p], [lo |-> p + 1, hi |-> iv.hi]})
  /\ pc' = "loop"
  /\ UNCHANGED origSeq
  /\ \A iv \in PickInterval : iv.lo # iv.hi
  /\ work' # {}

Terminate == /\ work = {} /\ pc' = "done" /\ UNCHANGED << seq, origSeq, work >>

Stall == /\ pc = "done" /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Terminate) /\ Stall

PCorrect == pc = "done" => /\ seq \in Permutations(origSeq)
                             /\ \A i \in 1 .. Len(seq) - 1 : seq[i] <= seq[i + 1]

\* The inductive invariant has three parts. The partitioning step builds
\* a laminar family of intervals (domains); each interval is always
\* sorted relative to the one immediately to its right; and the current
\* sequence is always a permutation of the input.
Inv ==
  /\ \A a \in work : \A b \in work : a # b => (a.hi < b.lo \/ b.hi < a.lo)
  /\ \A a, b \in work : a.hi + 1 = b.lo => \A i \in a.lo .. a.hi : seq[i] <= seq[i + 1]
  /\ seq \in Permutations(origSeq)

Termination == <>(pc = "done")

\* A finite version of Sequences.Seq for model checking; the name
\* Seq is inherited from Sequences and must not be redefined here.
LimitedSeq(n, S) == CHOOSE s \in SeqOf(S, n) : TRUE

====