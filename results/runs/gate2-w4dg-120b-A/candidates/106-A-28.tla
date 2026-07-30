---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Utility operators used across the key-value store specifications.
\* No actors or state: this module is purely functional.

CONSTANTS MaxCode, MaxSeq

\* Equality on functions interpreted as sets of pairs (required for Permutations).
RECURSIVE FuntSet(_)
FuntSet(f) == {<<x, y>> : y \in f[x]}

\* 1. Set overlap test.
Intersecting(s, t) == \E x \in s : x \in t

\* 2. Max/min from a set.
MaxSet(s) == CHOOSE x \in s : \A y \in s : y <= x
MinSet(s) == CHOOSE x \in s : \A y \in s : y >= x

\* 3. Generalized set reduction (fold over a set with an accumulator).
SetReduce(op, init, S) ==
  LET Fold[T \in SUBSET S] ==
    IF T = {} THEN init
    ELSE
      LET x == CHOOSE y \in T : TRUE
      IN op[x, Fold[T \ {x}]]
  IN Fold[S]

\* 4. Sequence reduction via a library fold operator.
SeqReduce(op, init, seq) == FoldSeq(seq, init, op)

\* 5. Index of an element in a sequence.
IndexOf(seq, e) ==
  CHOOSE i \in DOMAIN seq : seq[i] = e

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

\* 7. Last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* 8. Test if a sequence is empty.
Empty(seq) == Len(seq) = 0

\* 9. Remove all occurrences of an element from a sequence.
RemoveAll(seq, e) ==
  IF Empty(seq) THEN << >>
  ELSE
    IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
    ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

\* 10. Intersection of a set of sets.
Intersection(S) ==
  CHOOSE x \in S : \A y \in S : x \subseteq y

\* 11. All permutation sequences of a finite set.
Permutations(S) ==
  IF S = {} THEN {<< >>}
  ELSE
    \E p \in Permutations(S \ {CHOOSE x \in S : TRUE}) :
      {<<CHOOSE x \in S : TRUE>> \o p}

\* 12. Test helper that prints diagnostic info on failure.
ASSERT(expr, msg) ==
  IF expr THEN TRUE
  ELSE
    BEGIN
      PrintT("ASSERTION FAILED: " \o msg);
      FALSE
    END

\* The .cfg file expects the following identifiers to exist; they are
\* defined here as no-ops that do not interfere with the library operators.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====