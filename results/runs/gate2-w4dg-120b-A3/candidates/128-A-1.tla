---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

\* The model is checked against a .cfg that declares the constants below and
\* replaces the infinite Seq operator from Sequences with a bounded version.
CONSTANTS Values, MaxSeqLen

\* Sequence abstraction: a finite version of Sequences!Seq so the model stays
\* bounded. EXTENDS Sequences keeps the rest of the API available.
LimitedSeq == [n \in 0..MaxSeqLen |-> Seq(Values)]

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

NoWork == {}
Intervals == SUBSET (0..MaxSeqLen)
AtomicInterval == <<0, MaxSeqLen>>

TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ work \subseteq Intervals
  /\ pc \in {"main", "halt"}

Init ==
  /\ seq \in LimitedSeq
  /\ seq # <<>>
  /\ orig = seq
  /\ work = {AtomicInterval}
  /\ pc = "main"

\* A valid partition of the current sequence over an interval and pivot:
\* positions outside the interval are untouched, positions at or below the
\* pivot index are no greater than positions above it.
ValidPartition(s, intv, i) ==
  /\ [j \in DOMAIN s |->
       IF j \notin intv /\ j \in DOMAIN seq THEN seq[j] ELSE s[j]]
  /\ \A a \in intv, b \in intv :
       (a <= i /\ i < b) => s[a] <= s[b]

Step ==
  /\ pc = "main"
  /\ work # NoWork
  /\ \E intv \in work :
       /\ work' = work \ {intv}
       /\ IF intv[1] = intv[2]
            THEN work'
            ELSE
             /\ \E i \in intv[1]..intv[2] :
                  /\ \E s \in LimitedSeq :
                       /\ ValidPartition(s, intv, i)
                       /\ seq' = s
                  /\ work' = work' \cup {<<intv[1], i>>, <<i + 1, intv[2]>>}
  /\ pc' = pc
  /\ UNCHANGED orig

Terminate ==
  /\ pc = "main"
  /\ work = NoWork
  /\ pc' = "halt"
  /\ UNCHANGED <<seq, orig, work>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The final permutation must be sorted and must be a rearrangement of the
\* input. The invariant is the structured version that the proof is built on.
PCorrect ==
  /\ (pc = "halt") => (seq \in Permutations(orig))
  /\ (pc = "halt") => (Len(seq) = Len(orig))
  /\ (pc = "halt") => (b \in 1..Len(seq) => seq[b] <= seq[b + 1])

\* A bounded sort preserves all of the internal reasoning; the model only
\* tests it up to MaxSeqLen, so the invariant stays checkable.
Inv ==
  /\ DomainsArePartitions(work)
  /\ PermutationPreserved(seq, orig)
  /\ RelativeSortedness(seq, work)

Termination == (pc = "halt")

PCORRECT == PCorrect
TYPEOK == TypeOK
INVARIANT == Inv

====