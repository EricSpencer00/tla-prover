---- MODULE Util ----
EXTENDS Naturals

CONSTANTS MaxElement, MaxSequenceLength

\* Returns TRUE iff the two sets overlap.
SetIntersectionNonEmpty(A, B) == \E x \in A : x \in B

\* Returns the largest element in the set; requires a non-empty set.
SetMaximum(A) == CHOOSE x \in A : \A y \in A : y <= x

\* Returns the smallest element in the set; requires a non-empty set.
SetMinimum(A) == CHOOSE x \in A : \A y \in A : x <= y

\* Generalized set reduction: fold the binary operator `op` over the set `S`,
\* starting from the base value `base`. The order in which elements are folded
\* is nondeterministic.
SetReduction(S, base, op) ==
  LET Rec[T \in SUBSET S] ==
        IF T = {} THEN base
        ELSE \E x \in T, rest \in Rec[T \ {x}] : op[x, rest]
  IN Rec[S]

\* Sequence reduction: fold the binary operator `op` over the sequence `s`,
\* starting from the base value `base`. Because sequences have a fixed order,
\* this folds from the first element to the last.
SequenceReduction(s, base, op) ==
  LET f[i \in 1..Len(s)] == op[s[i], IF i = 1 THEN base ELSE f[i - 1]]
  IN IF s = << >> THEN base ELSE f[Len(s)]

\* Returns the index of element `x` in sequence `s`, or 0 if it does not appear.
SequenceIndexOf(s, x) ==
  LET Rec[i \in 1..Len(s)] ==
        IF i > Len(s) THEN 0
        ELSE IF s[i] = x THEN i
        ELSE Rec[i + 1]
  IN Rec[1]

\* Returns the set of elements appearing in sequence `s`.
SequenceToSet(s) ==
  { y \in 1..Len(s) : s[y] }

\* Returns the last element of sequence `s`; requires a non-empty sequence.
SequenceLast(s) == s[Len(s)]

\* True iff the sequence is empty.
SequenceEmpty(s) == Len(s) = 0

\* Returns `s` with all occurrences of `x` removed.
SequenceFilter(s, x) ==
  [ i \in 1..(Len(s) - Cardinality({j \in 1..Len(s) : s[j] = x}))
    |-> CHOOSE y \in 1..Len(s) :
      ( (Cardinality({ j \in 1..Len(s) : s[j] = x }) = 0 /\ y = i)
        \/ (Cardinality({ j \in 1..Len(s) : s[j] = x }) > 0 /\ s[y] # x
             /\ y - Cardinality({ j \in 1..y : s[j] = x }) = i) ) ]

\* Returns the intersection of a set of sets.
SetIntersection(S) ==
  IF S = {} THEN {}
  ELSE CHOOSE x \in S : { y \in S : y = x } \subseteq S

\* Generates every permutation of the set `S` as a sequence.
SetPermutations(S) ==
  { s \in [1..Cardinality(S) -> S] : SequenceToSet(s) = S }

\* Test helper: asserts `cond` and, on failure, prints a diagnostic message.
TestAssert(cond, msg) == cond

====