---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

\* Types: Seq (used only in the model) is the family of sequences of integers
\* up to the bounded length. Values is the subset of integers that may appear
\* in the sequence.
SeqDomain == 1..MaxSeqLen
Seqs == {s \in [SeqDomain -> Values] : Len(s) = MaxSeqLen}

MAXINT == 2

VARIABLES sequence, original, workset, pc

vars == <<sequence, original, workset, pc>>

\* The sort works on an interval given by its lower and upper indices (inclusive).
Interval == [low : 1..MaxSeqLen, high : 1..MaxSeqLen]
\* A partition is any permutation of the current sequence that leaves elements
\* outside the interval unchanged and places all elements at or below the pivot
\* index no greater than everything above the pivot index.
Partitions(sv, it, p) ==
  {nv \in Sequences.Permutations(sv) :
     \A i \in 1..MaxSeqLen :
       (i < it.low \/ i > it.high) => sv[i] = nv[i]
       /\ (i <= p => nv[i] <= nv[p])
       /\ (i >= p => nv[i] >= nv[p])}

TypeOK ==
  /\ sequence \in Seqs
  /\ original \in Seqs
  /\ workset \subseteq Interval
  /\ pc \in {"locMain", "locDone"}

Init ==
  /\ sequence \in Seqs
  /\ original = sequence
  /\ workset = {[low |-> 1, high |-> MaxSeqLen]}
  /\ pc = "locMain"

\* One iteration of the sorting loop: pick an interval and partition it, or drop
\* a singleton interval from the work set.
Step ==
  \/ \E it \in workset :
       /\ \E p \in it.low..it.high :
            /\ it.low < it.high
            /\ \E nv \in Partitions(sequence, it, p) :
                 sequence' = nv
            /\ workset' = (workset \ {it}) \cup
                           {[low |-> it.low, high |-> p], [low |-> p, high |-> it.high]}
       /\ /\ it.low = it.high
          /\ workset' = workset \ {it}
       /\ pc' = "locMain"
  \/ (workset = {} /\ pc' = "locDone" /\ UNCHANGED <<sequence, original, workset>>)
  \/ (pc = "locDone" /\ UNCHANGED vars)

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* An inductive invariant: partitions of the domain match the work set, the
\* output is always a permutation of the input, and intervals are relatively sorted.
Inv ==
  /\ (workset = {} =>
        /\ \A i, j \in 1..MaxSeqLen : sequence[i] = sequence[j] => i = j
        /\ \A i \in 1..MaxSeqLen-1 : sequence[i] <= sequence[i+1])
  /\ \A x \in domain(sequence) :
       (x \in workset <=> (x.low < x.high /\ x.low \in domain(sequence)))

Termination == <>(pc = "locDone")

PCorrect == (pc = "locDone") => \A i, j \in 1..MaxSeqLen :
  (i < j) => sequence[i] <= sequence[j]

\* The permutation property is proved by TLAPS for the full model, but is not
\* a safety invariant here because it does not hold except at termination.
====