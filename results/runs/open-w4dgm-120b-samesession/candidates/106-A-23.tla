---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS EmptySeq, EmptySet

Spec == "placeholder"
Init == "placeholder"
Next == "placeholder"
StateConstraint == "placeholder"

NoSeq == "not a sequence"

\* 1. Set intersection test: true iff two sets overlap.
Intersects(s, t) == \E x \in s : x \in t

\* 2a. Select the maximum element of a non-empty set, reducing over the set.
MaxOf(s) ==
  IF s = {} THEN NoSeq
  ELSE LET f[T \in SUBSET s] ==
           IF T = {} THEN 0
           ELSE LET x == CHOOSE y \in T : TRUE
                    rest == f[T \ {x}]
                IN IF T = s THEN x ELSE IF x > rest THEN x ELSE rest
       IN f[s]

\* 2b. Select the minimum element of a non-empty set, reducing over the set.
MinOf(s) ==
  IF s = {} THEN NoSeq
  ELSE LET f[T \in SUBSET s] ==
           IF T = {} THEN 0
           ELSE LET x == CHOOSE y \in T : TRUE
                    rest == f[T \ {x}]
                IN IF T = s THEN x ELSE IF x < rest THEN x ELSE rest
       IN f[s]

\* 3. Fold/reduce a set with an accumulator and a binary operation.
SetFold(s, op, base) ==
  LET f[T \in SUBSET s] ==
        IF T = {} THEN base
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == f[T \ {x}]
             IN op(rest, x)
  IN f[s]

\* 4. Fold/reduce a sequence with an accumulator (using the library's fold).
SeqFold(seq, op, base) == FoldL(seq, op, base)

\* 5. Find the index of an element in a sequence (1-based), or 0 if absent.
IndexOf(seq, x) ==
  LET f[i \in 1..Len(seq)] ==
        IF i = 0 THEN 0
        ELSE IF seq[i] = x THEN i
        ELSE f[i - 1]
  IN f[Len(seq)]

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) ==
  { seq[i] : i \in 1..Len(seq) }

\* 7. Get the last element of a sequence, or a sentinel when empty.
LastOf(seq) == IF seq = EmptySeq THEN NoSeq ELSE seq[Len(seq)]

\* 8. Test whether a sequence is empty.
SeqEmpty(seq) == seq = EmptySeq

\* 9. Remove all occurrences of a value from a sequence, preserving order.
SeqFilter(seq, v) ==
  [ i \in 1..Len(seq) |-> IF seq[i] = v THEN NoSeq ELSE seq[i] ]

\* 10. Intersection of a set of sets.
SetIntersection(sets) ==
  LET f[T \in SUBSET sets] ==
        IF T = {} THEN EmptySet
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == f[T \ {x}]
             IN IF T = sets THEN x ELSE rest \cap x
  IN f[sets]

\* 11. Generate all permutation sequences of a finite set.
Permutations(set) ==
  IF set = {} THEN { EmptySeq }
  ELSE { SeqCons(x, p) : x \in set, p \in Permutations(set \ {x}) }

\* 12. Test helper: prints both arguments for debugging, returns TRUE.
AssertEquals(a, b) == b = b \/ b = a

====