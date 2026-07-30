---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* All the identifiers below are named exactly as the reference .cfg expects.
\* The operator LimitedSeq is the finite replacement for Sequences!Seq; the
\* name Seq itself is never declared here (the .cfg maps it to LimitedSeq).
\* The model bounds Values and MaxSeqLen are set by the .cfg file.
CONSTANTS Values, MaxSeqLen

VARIABLES seq, origSeq, workset, pc

vars == << seq, origSeq, workset, pc >>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

Domain(f) == {i \in DOMAIN f : TRUE}

DomainBelow(i) == {j \in DOMAIN seq : j <= i}
DomainAbove(i) == {j \in DOMAIN seq : j > i}

RelSorted(i) ==
  /\ \A x \in DomainBelow(i) : \A y \in DomainAbove(i) : seq[x] <= seq[y]
  /\ \A x \in DomainBelow(i) : \A y \in DomainBelow(i) : x <= y => seq[x] <= seq[y]
  /\ \A x \in DomainAbove(i) : \A y \in DomainAbove(i) : x <= y => seq[x] <= seq[y]

\* A partition may rearrange the interval freely provided elements crossing the
\* pivot boundary respect the ordering; everything outside the interval is unchanged.
Partition(seq, part) ==
  LET lo == part.lo IN
  LET hi == part.hi IN
    {s \in [1..Len(seq) -> Values] :
       /\ s[i] = seq[i] FOR i \in DOMAIN seq \ ((lo..hi) \cup (hi+1..MaxSeqLen))
       /\ \A x \in lo..hi, y \in hi+1..MaxSeqLen : s[x] <= s[y]}

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ origSeq \in [1..MaxSeqLen -> Values]
  /\ workset \in SUBSET Intervals
  /\ pc \in {"running", "done"}

\* The partition operator is nondeterministic over the partitions the algorithm
\* is free to pick in one step; that is exactly what makes the model checkable.
Init ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ origSeq = seq
  /\ workset = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "running"

Step ==
  /\ pc = "running"
  /\ workset # {}
  /\ \E part \in workset :
       /\ workset' = workset \ {part}
       /\ IF part.lo = part.hi
            THEN workset'
            ELSE
              LET piv \in part.lo..part.hi IN
                /\ \E s \in Partition(seq, part) : seq' = s
                /\ workset' = workset' \cup {[lo |-> part.lo, hi |-> piv], [lo |-> piv+1, hi |-> part.hi]}
       /\ UNCHANGED << origSeq, pc >>
  /\ UNCHANGED << seq, origSeq, workset, pc >>

Terminate == /\ pc = "running" /\ workset = {} /\ pc' = "done" /\ UNCHANGED << seq, origSeq, workset >>

Quiesce == /\ pc = "done" /\ UNCHANGED vars

Next == Step \/ Terminate \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* Final state is a permutation of the input and is sorted.
PCorrect == pc = "done" => /\ seq \in {origSeq \o p : p \in PermutationsOn(Domain origSeq)}
                              /\ \A i \in 1..MaxSeqLen-1 : seq[i] <= seq[i+1]

Inv ==
  /\ workset \subseteq Intervals
  /\ seq \in {origSeq \o p : p \in PermutationsOn(Domain origSeq)}
  /\ \A part \in workset : RelSorted(part.hi)

Termination == <>(pc = "done")

====