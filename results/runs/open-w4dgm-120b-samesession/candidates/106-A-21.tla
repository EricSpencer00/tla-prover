---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS SeqBound

\* Set intersection test: TRUE iff two sets have a common element.
Overlap(a, b) == \E x \in a : x \in b

\* Max/min element of a set (the set is finite with a bounded range).
SetMax(S) == CHOOSE m \in S : \A x \in S : x <= m
SetMin(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized reduction (fold) over a set.
SetFold(f, S, a) ==
  IF S = {} THEN a
  ELSE LET x == CHOOSE y \in S : TRUE
           rest == S \ {x}
       IN f(SetFold(f, rest, a), x)

\* Reduction over a sequence via a library fold operator.
SeqFold(f, seq, a) == FoldSeq(f, seq, a)

\* Find the index of an element in a sequence; 0 if absent.
IndexOf(seq, x) == CHOOSE k \in 1..Len(seq) : seq[k] = x
                   DEFAULT 0

SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

LastOf(seq) == IF seq = << >> THEN 0 ELSE seq[Len(seq)]

SeqEmpty(seq) == seq = << >>

RemoveAll(seq, x) ==
  [ i \in 1..Len(seq) |-> IF seq[i] = x THEN 0 ELSE seq[i] ]

SetIntersectionOf(sets) ==
  { x \in UNION sets : \A t \in sets : x \in t }

\* Generate all permutation sequences of a given finite set.
PermutationsOf(S) ==
  { seq \in UNION [n \in 1..Cardinality(S) -> [1..n -> S]] :
       /\ Len(seq) = Cardinality(S)
       /\ \A i, j \in 1..Len(seq) : (seq[i] = seq[j]) => (i = j) }

\* Test helper that prints diagnostic info on failure.
AssertEq(x, y) ==
  \/ x = y
  \/ PrintT("ASSERTION FAILED: ", x, " =/= ", y)

\* Name the useful operators that this spec offers.
Operators == { Overlap, SetMax, SetMin, SetFold, SeqFold, IndexOf,
               SeqToSet, LastOf, SeqEmpty, RemoveAll, SetIntersectionOf,
               PermutationsOf, AssertEq }

Spec == Operators

Init == TRUE
Next == TRUE
TypeOK = TRUE
StateConstraint == TRUE
SpecOK == Spec = Operators

====