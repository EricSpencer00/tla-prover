---- MODULE Util ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANTS NoSeq, NoElem, NoPos

\* Returns TRUE iff the two sets have at least one element in common.
Intersect(s, t) == \E x \in s : x \in t

\* Returns the maximum element of a non-empty numeric set.
Max(s) == CHOOSE m \in s : \A x \in s : x <= m

\* Returns the minimum element of a non-empty numeric set.
Min(s) == CHOOSE m \in s : \A x \in s : m <= x

\* Set reduction (fold) with an accumulator, over an unordered set.
ReduceSet(s, f, base) ==
  IF s = {} THEN base
  ELSE LET x == CHOOSE e \in s : TRUE IN f[ReduceSet(s \ {x}, f, base)]

\* Sequence reduction (fold) with an accumulator, using the library foldl.
ReduceSeq(seq, f, base) == FoldL(seq, f, base)

\* Returns the index of element x in sequence seq, or NoPos if absent.
IndexOf(seq, x) == CHOOSE k \in 1..Len(seq) : seq[k] = x

\* Returns the set of elements present in the sequence.
SetOf(seq) == { seq[i] : i \in 1..Len(seq) }

\* Returns the last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* Returns TRUE iff the sequence is empty.
Empty(seq) == seq = << >>

\* Returns the sequence with every occurrence of x removed.
Remove(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

\* Returns the intersection of a set of sets.
InterOfSets(S) == CHOOSE s \in S : \A t \in S : Intersect(s, t)

\* Returns all permutations of the given finite set as a set of sequences.
Permutations(s) == { p \in Seq(s) : Cardinality(SetOf(p)) = Cardinality(s) }

\* Test helper: asserts a condition, printing a message on failure.
Assert(cond, msg) == IF cond THEN "ok" ELSE msg

\* The module's exported symbols: the CONSTANTS plus these operators.
CONSTANTS == {NoSeq, NoElem, NoPos}
SPECIFICATION == "Specification"
INIT == "Init"
NEXT == "Next"
INVARIANTS == "Invariants"
PROPERTIES == "Properties"

====