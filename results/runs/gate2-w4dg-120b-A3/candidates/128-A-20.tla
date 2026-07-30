---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Values, MaxSeqLen

Indices == 1..MaxSeqLen
Interval == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
Automorphism == [1..MaxSeqLen -> 1..MaxSeqLen]
Operand == UNION {Seq(V) : V \in SUBSET Values}

\* An automorphism must be a bijection; it's a permutation of the index domain.
Permutation == { f \in Automorphism : \A x \in DOMAIN f : \A y \in DOMAIN f :
                  (f[x] = f[y]) => (x = y) }

Bounded == Cardinality(Values) =< 2 /\ MaxSeqLen = 3

VARIABLES seq, original, work, pc
vars == <<seq, original, work, pc>>

TypeOK ==
    /\ seq \in Operand /\ original \in Operand
    /\ work \subseteq Interval
    /\ pc \in {"loop", "done"}

Init ==
    /\ \E v \in Operand : seq = v
    /\ original = seq
    /\ work = {[lo |-> 1, hi |-> Len(seq)]}
    /\ pc = "loop"

\* The partition operator: elements outside the interval are unchanged, and
\* elements at or below the pivot index are no greater than those above it.
Partition(seq, i, p) ==
    { v \in Operand :
        /\ \A x \in DOMAIN v : v[x] = seq[x]
        /\ \A x \in DOMAIN v : (i <= x /\ x <= p) => v[x] <= v[p]
        /\ \A x \in DOMAIN v : (p < x /\ x <= i) => v[p] <= v[x] }

\* The sorting loop, abstracted away from the actual partition algorithm.
SortStep ==
    \/ \E r \in work :
         /\ r.lo = r.hi
         /\ work' = work \ {r}
         /\ UNCHANGED <<seq, original, pc>>
    \/ \E r \in work, p \in Indices :
         /\ r.lo < r.hi
         /\ p \in r.lo..r.hi
         /\ \E new \in Partition(seq, r.hi, p) :
              /\ seq' = new
              /\ work' = (work \ {r}) \cup {[lo |-> r.lo, hi |-> p],
                                          [lo |-> p + 1, hi |-> r.hi]}
         /\ UNCHANGED <<original, pc>>
    \/ (work = {} /\ pc' = "done" /\ UNCHANGED <<seq, original, work>>)
    \/ (pc = "done" /\ UNCHANGED vars)

Next == SortStep

Spec == Init /\ [][Next]_vars
        /\ WF_vars(SortStep)

PermutationOfOriginal ==
    \E f \in Permutation : original = [x \in DOMAIN seq |-> seq[f[x]]]

Sorted ==
    \A i \in DOMAIN seq : i + 1 \in DOMAIN seq => seq[i] <= seq[i + 1]

PCorrect ==
    (pc = "done") => (PermutationOfOriginal /\ Sorted)

\* The inductive invariant: intervals are disjoint and cover the whole domain,
\* each value appears the same number of times in the original and current seq,
\* and no value outside a processed interval is out of order with one inside it.
Inv ==
    /\ \A i \in DOMAIN seq :
        \/ i \in UNION {1..(r.hi) : r \in work}
        \/ (i + 1 \in UNION {1..(r.hi) : r \in work} /\ seq[i] <= seq[i + 1])
    /\ \A v \in Values : Cardinality({i \in DOMAIN seq : seq[i] = v})
                          = Cardinality({i \in DOMAIN original : original[i] = v})

Termination == (pc = "done")

====