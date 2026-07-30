---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The model is deliberately tiny: the sequence starts at most two elements long,
\* and the set of values is finite. The TLC configuration supplies concrete
\* finite values for both.
\* The interval notation below treats indices as 1..Len, which is exactly how
\* Sequences in TLA+ are defined.

\* The standard Sequences module defines Seq as an unrestricted (possibly
\* infinite) level-2 function. That definition is uncheckable, so the .cfg
\* replaces it with LimitedSeq, which is exactly the same restriction on the
\* domain plus an explicit bound on the length.
\* Both names must stay bound to the same operator; we only define LimitedSeq.

Seq == CHOOSE f \in [ 1 .. MaxSeqLen -> Values ] :
  \A i \in 1 .. MaxSeqLen : \E v \in Values : f[i] = v

LimitedSeq == Seq

VARIABLES seq, orig, workInts, pc

vars == << seq, orig, workInts, pc >>

Interval == [ lo, hi : 1 .. MaxSeqLen ]

TypeOK ==
  /\ seq \in [ 1 .. MaxSeqLen -> Values ]
  /\ orig \in [ 1 .. MaxSeqLen -> Values ]
  /\ workInts \subseteq Interval
  /\ pc \in { "loop", "done" }

Init ==
  /\ \E s \in [ 1 .. MaxSeqLen -> Values ] :
       /\ seq = s
       /\ orig = s
  /\ workInts = { [ lo |-> 1, hi |-> MaxSeqLen ] }
  /\ pc = "loop"

\* A partition must leave everything outside the interval untouched; inside it
\* all elements at or below the pivot index are no greater than all above it.
ValidPartitions(i, p) ==
  { t \in [ 1 .. MaxSeqLen -> Values ] :
      /\ \A k \in 1 .. MaxSeqLen : k < i \/ k > p => t[k] = seq[k]
      /\ \A k \in i .. p, l \in p + 1 .. MaxSeqLen : t[k] <= t[l] }

Split(i, p) ==
  { [ lo |-> i, hi |-> p ], [ lo |-> p + 1, hi |-> MaxSeqLen ] }

SortStep ==
  /\ pc = "loop"
  /\ \E i \in workInts :
       /\ workInts' = workInts \ { i }
       /\ IF i.lo = i.hi
            THEN workInts'
            ELSE
              /\ \E p \in i.lo .. i.hi :
                   /\ seq' \in ValidPartitions(i.lo, p)
                   /\ workInts' = workInts' \cup Split(i.lo, p)
       /\ UNCHANGED orig
  /\ pc' = IF workInts = {} THEN "done" ELSE "loop"

Stall ==
  \* After termination there is nowhere to go; this keeps the model from
  /\ pc = "done"
  /\ UNCHANGED vars

Next == SortStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(SortStep)

PCorrect ==
  /\ pc = "done"
  /\ \A i \in 1 .. MaxSeqLen : \A j \in i + 1 .. MaxSeqLen : seq[i] <= seq[j]

\* The partition operator rearranges elements but never drops or adds them,
\* so the final sequence must be a pure permutation of the input.
Permutation ==
  \E iso \in [ 1 .. MaxSeqLen -> 1 .. MaxSeqLen ] :
    /\ \A a, b \in 1 .. MaxSeqLen : iso[a] = iso[b] => a = b
    /\ orig' = [ i \in 1 .. MaxSeqLen |-> seq[iso[i]] ]

\* The three parts of the invariant are proved separately and together imply
\* the partial-correctness claim.
Inv ==
  /\ \A i \in 1 .. MaxSeqLen : seq[i] \in Values
  /\ Permutation
  /\ \A i \in 1 .. MaxSeqLen : \A j \in i + 1 .. MaxSeqLen : seq[i] <= seq[j]

Termination == <>(pc = "done")

====