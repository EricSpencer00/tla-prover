---- MODULE Util ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  MaxVal

\* Operators available to other spec modules.

\* Set intersection test: TRUE iff sets a and b have a non-empty overlap.
SetOverlap(a, b) == \E x \in a : x \in b

\* Maximum element in a non-empty set.
MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

\* Minimum element in a non-empty set.
MinOf(S) == CHOOSE x \in S : \A y \in S : y >= x

\* General set reduction (fold) with an accumulator.
FoldSet(f, S, base) ==
  LET go[X \in SUBSET S] ==
    IF X = {} THEN base
    ELSE \E y \in X : go[X \ {y}] @ f(y)
  IN go[S]

\* Sequence reduction; uses the library FoldSeq operator.
FoldSeq(f, s, base) == FoldSeq(f, s, base)

\* Find the index of a target element in a sequence, or -1 if absent.
SeqIndex(s, target) ==
  CHOOSE i \in -1..Len(s) : (\E j \in 1..Len(s) : (s[j] = target) <=> (j = i))

\* Convert a sequence to the set of its elements.
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* The last element of a sequence, or -1 on the empty sequence.
SeqLast(s) == IF s = << >> THEN -1 ELSE s[Len(s)]

\* TRUE iff a sequence is empty.
SeqEmpty(s) == s = << >>

\* Remove all occurrences of a value from a sequence.
SeqRemove(s, val) ==
  IF s = << >> THEN << >>
  ELSE IF Head(s) = val THEN SeqRemove(Tail(s), val)
  ELSE << Head(s) >> \o SeqRemove(Tail(s), val)

\* Intersection of a set of sets.
SetIntersect(S) ==
  IF S = {} THEN {}
  ELSE LET x \in S IN \A y \in S : y \subseteq x

\* Generate all permutations of a finite set as sequences.
AllPermutations(S) ==
  IF S = {} THEN { << >> }
  ELSE
    { << x >> \o p : x \in S, p \in AllPermutations(S \ {x}) }

\* Test helper: raises an error with a diagnostic message when its argument is FALSE.
TestHelper(b, msg) == IF b THEN TRUE ELSE CHOOSE z \in -1..0 : FALSE

\* No actor or system component to model; the spec uses these operators only.
Spec == TRUE
Init == TRUE
Next == TRUE

TypeOK == TRUE
SpecOk == TRUE

====