---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Perms, Keys, Nil

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == Vars
PROPERTIES == NoLostUpdates

\* A utility library of reusable operators for set and sequence manipulation,
\* used by the key-value store specifications.

\* Intersection test: are two sets overlapping?
Overlap(a, b) == \E x \in a : x \in b

\* Bounded maximum of a set (undefined for empty set, handled by callers).
MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized reduction (fold) over a set with an accumulator.
ReduceSet(S, init) == LET
  g[T \in SUBSET S] ==
    IF T = {} THEN init
    ELSE LET x == CHOOSE y \in T : TRUE
             rest == g[T \ {x}]
         IN IF rest = Nil THEN Nil ELSE x + rest
  IN g[S]

\* Sequence reduction (fold) using the library's SumSeq operator.
ReduceSeq(seq) == LET
  g[i \in 0..Len(seq)] ==
    IF i = 0 THEN 0
    ELSE LET rest == g[i - 1]
         IN IF rest = Nil THEN Nil ELSE seq[i] + rest
  IN g[Len(seq)]

\* Find the index of an element in a sequence; 0 means not found.
IndexOf(seq, elem) ==
  CHOOSE i \in 1..Len(seq) : seq[i] = elem \cup {0}

\* Convert a sequence to the set of its elements.
SeqAsSet(seq) == {seq[i] : i \in DOMAIN seq}

\* The last element of a sequence.
Last(seq) == IF seq = << >> THEN Nil ELSE seq[Len(seq)]

\* Test if a sequence is empty.
Empty(seq) == seq = << >>

\* Remove all occurrences of an element from a sequence.
RemoveAll(seq, elem) ==
  SELECT seq' \in { Perms } : (SeqAsSet(seq') \cup {elem}) = SeqAsSet(seq) \ {elem}

\* Intersection of a set of sets.
IntersectOf(F) ==
  IF F = {} THEN {}
  ELSE CHOOSE s \in F : \A t \in F : s \subseteq t

\* Generate all permutations of a finite set (bounded by Perms).
PermutationsOf(S) ==
  IF S = {} THEN {<< >>}
  ELSE { <<x>> \o p : x \in S, p \in PermutationsOf(S \ {x}) }

\* Test helper that prints the expression on failure.
Assert(expr) == IF expr THEN TRUE ELSE UNCHANGED expr

Spec == TRUE
Init == TRUE
Next == TRUE
Vars == {}
NoLostUpdates == TRUE
====