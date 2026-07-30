---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Replaces Seq from the standard module with a finite version so the model
\* is checkable; the name on the left must stay undefined in this file.
LimitedSeq(S) == CHOOSE f \in [ 1 .. Len(S) -> 1 .. Len(S) ] :
                     \A i \in 1 .. Len(S) : f[i] = i

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, workset, pc
vars == << seq, orig, workset, pc >>

\* An interval is a contiguous range of sequence indices.
Interval == [ lo : 1 .. MaxSeqLen, hi : 1 .. MaxSeqLen ]

InDomain(i, intv) == intv.lo <= i /\ i <= intv.hi

\* The partition operator: any permutation that leaves elements outside the
\* chosen interval alone and puts every element at or below the pivot index
\* no greater than every element above it.
Partition(S, intv, p) == { T \in [ 1 .. Len(S) -> Values ] :
  /\ \A i \in 1 .. Len(S) : ~InDomain(i, intv) => T[i] = S[i]
  /\ \A i, j \in 1 .. Len(S) :
       InDomain(i, intv) /\ InDomain(j, intv) /\ i <= p /\ p < j
         => T[i] <= T[j] }

\* Permutations written as composition with automorphisms of the domain.
Permutation(T, S) == \E f \in [ 1 .. Len(S) -> 1 .. Len(S) ] :
  /\ \A i \in 1 .. Len(S) : T[i] = S[f[i]]
  /\ \A i, j \in 1 .. Len(S) : f[i] = f[j] => i = j

Sorted(Q) == \A i \in 1 .. Len(Q) - 1 : Q[i] <= Q[i + 1]

TypeOK ==
  /\ seq \in [ 1 .. MaxSeqLen -> Values ]
  /\ orig \in [ 1 .. MaxSeqLen -> Values ]
  /\ workset \subseteq Interval
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E S \in { s \in [ 1 .. MaxSeqLen -> Values ] : Len(s) > 0 } :
       /\ seq = S
       /\ orig = S
  /\ workset = { [ lo |-> 1, hi |-> Len(seq) ] }
  /\ pc = "loop"

\* A no-op available after termination; without it the model would deadlock
\* once all intervals have been processed (per the cfg's DEADLOCK FALSE).
Stuck == UNCHANGED vars

Backtrack ==
  \/ \E intv \in workset :
       /\ workset' = workset \ { intv }
       /\ pc' = IF workset \ { intv } = {} THEN "done" ELSE pc
       /\ UNCHANGED << seq, orig >>
  \/ \E intv \in workset, p \in 1 .. Len(seq) :
       /\ InDomain(p, intv)
       /\ intv.hi > intv.lo
       /\ \E T \in Partition(seq, intv, p) :
            /\ seq' = T
            /\ workset' = (workset \ { intv })
                 \cup { [ lo |-> intv.lo, hi |-> p ], [ lo |-> p + 1, hi |-> intv.hi ] }
            /\ pc' = IF (workset \ { intv })
                 \cup { [ lo |-> intv.lo, hi |-> p ], [ lo |-> p + 1, hi |-> intv.hi ] } = {}
                 THEN "done" ELSE pc
            /\ UNCHANGED orig
  \/ Stuck

Next == Backtrack

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Backtrack)

DomainPartitions ==
  /\ \A intv \in workset : \A i \in 1 .. Len(seq) : InDomain(i, intv) => seq[i] <= seq[intv.hi]

Inv == DomainPartitions /\ Permutation(seq, orig) /\ Sorted([ i \in 1 .. Len(seq) : seq[i] ])

PCorrect == pc = "done"
Termination == pc = "done"
====