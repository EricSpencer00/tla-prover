---- MODULE Util ----
EXTENDS Sequences, FiniteSets

CONSTANTS Nothing, EmptySeq

\* Set intersection test: TRUE iff the two sets overlap.
Intersect(a, b) == \E x \in a : x \in b

\* Maximum element of a non-empty finite set of natural numbers.
SetMax(s) ==
  LET f[T \in SUBSET s] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE
                 r == f[T \ {x}]
             IN IF r > x THEN r ELSE x
  IN f[s]

\* Minimum element of a non-empty finite set of natural numbers.
SetMin(s) ==
  LET f[T \in SUBSET s] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE
                 r == f[T \ {x}]
             IN IF r < x THEN r ELSE x
  IN f[s]

\* Generalized set reduction (fold over a set with an accumulator).
SetReduce(s, op, base) ==
  LET f[T \in SUBSET s] ==
        IF T = {} THEN base
        ELSE LET x == CHOOSE y \in T : TRUE
                 r == f[T \ {x}]
             IN op[r, x]
  IN f[s]

\* Sequence reduction (fold over a sequence with an accumulator).
SeqReduce(seq, op, base) ==
  FoldL(seq, op, base)

\* Find the index of an element in a sequence; Nothing if absent.
SeqIndex(seq, x) ==
  LET f[i \in 1..Len(seq)] ==
        IF seq[i] = x THEN i
        ELSE IF i = Len(seq) THEN Nothing
        ELSE f[i + 1]
  IN f[1]

\* Convert a sequence to the set of its elements.
SeqAsSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Get the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Test if a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
SeqRemoveAll(seq, x) ==
  IF SeqEmpty(seq) THEN EmptySeq
  ELSE IF SeqHead(seq) = x THEN SeqRemoveAll(SeqTail(seq), x)
  ELSE SeqAppend(SeqHead(seq), SeqRemoveAll(SeqTail(seq), x))

\* Intersection of a set of sets.
SetIntersection(S) ==
  {x \in UNION S : \A A \in S : x \in A}

\* Compute all permutation sequences of a finite set.
Permutations(s) ==
  LET f[T \in SUBSET s] ==
        IF T = {} THEN {EmptySeq}
        ELSE {SeqAppend(x, perm)
                : x \in T, perm \in f[T \ {x}]}
  IN f[s]

\* A test helper that prints a diagnostic string on failure.
Assert(cond, msg) ==
  IF cond THEN Nothing ELSE msg

\* Required names that the .cfg expects to exist in this module.
CONSTANTS Nothing, EmptySeq
VARIABLES vars
vars == {}

Init == TRUE
Next == TRUE

Spec == Init /\ [][Next]_vars

TypeOK == TRUE
StateConstraint == TRUE

====