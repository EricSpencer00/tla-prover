---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* Sequence operators are inherited from the standard Sequences module. The
\* .cfg replaces Seq with a limited, FINITE version that keeps model checking
\* tractable. The name on the left side must NOT be re-declared here.
LimitedSeq(n, f) == Seq(n, f)

VARIABLES seq, input, intervals, pc
vars == <<seq, input, intervals, pc>>

\* The work set holds intervals still to partition; there is a single
\* sequential sort actor, so the step relation below is deterministic apart
\* from the nondeterministic choice of partition result.
Space(n) == UNION { 1 .. n }

TypeOK ==
  /\ seq \in [Space(MaxSeqLen) -> Values]
  /\ input \in [Space(MaxSeqLen) -> Values]
  /\ intervals \subseteq [lo : 1 .. MaxSeqLen, hi : 1 .. MaxSeqLen]
  /\ pc \in {"sorting", "done"}

Domain(c) == { i \in 1..MaxSeqLen : c[i] # input[i] }
NoCross(i, j, k) ==
  /\ j \in Domain(i)
  /\ k \in Domain(i)
  /\ j < k
  /\ \A m \in 1..MaxSeqLen : (m < j \/ k < m) => i[m] = input[m]

\* Permutations of the original sequence: a permutation of a partial domain
\* is a bijection on the indices on which the permutation changes something.
Permutation == { c \in [Space(MaxSeqLen) -> Values] :
  /\ \A m \in 1..MaxSeqLen : c[m] \in Values
  /\ \E g \in [Domain(c) -> Domain(c)] : g \in (Domain(c) <-> Domain(c))
     /\ \A x \in Domain(c) : c[x] = input[g[x]] }

\* A partition stores the ordering guarantee across the pivot index only
\* where the interval is non-empty; an empty interval is left untouched.
Partitions(c, l, h) ==
  /\ \A i \in 1..MaxSeqLen : i < l \/ h < i => c[i] = seq[i]
  /\ \A i \in l..h : c[i] \in Values
  /\ \A i \in l..h, j \in l..h : i <= j => c[i] <= c[j]

Init ==
  /\ \E s \in [Space(MaxSeqLen) -> Values] : seq = s
  /\ input = seq
  /\ intervals = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "sorting"

Sorted ==
  \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i + 1]

PartitionStep ==
  \/ \E it \in intervals :
       \/ /\ it.lo = it.hi
          /\ intervals' = intervals \ {it}
       \/ \E p \in it.lo .. it.hi :
            \E c \in [Space(MaxSeqLen) -> Values] :
              /\ Partitions(c, it.lo, it.hi)
              /\ c[p] = seq[p]
              /\ seq' = c
              /\ intervals' = (intervals \ {it})
                 \cup {[lo |-> it.lo, hi |-> p], [lo |-> p + 1, hi |-> it.hi]}
  /\ pc' = "sorting"
Termination ==
  pc = "done" /\ UNCHANGED vars
Idle ==
  LET s == CHOOSE x \in space : TRUE \/ UNCHANGED vars IN s

Next == PartitionStep \/ Termination \/ Idle

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep)

\* A permutation of the input that is sorted is exactly a correctly sorted
\* output; that is what the partial correctness invariant protects against.
PCorrect ==
  (pc = "done") => (seq \in Permutation /\ Sorted)

Inv ==
  /\ \A it \in intervals : it.lo <= it.hi
  /\ seq \in Permutation
  /\ \A it \in intervals :
       \A i \in it.lo .. it.hi, j \in it.lo .. it.hi : i <= j => seq[i] <= seq[j]

Termination == <>(pc = "done")
====