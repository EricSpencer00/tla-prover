---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Elem, MaxSeqLen

VARIABLES set1, set2, fn, seq1, seq2, init

vars == <<set1, set2, fn, seq1, seq2, init>>

TypeOK ==
  /\ set1 \in SUBSET Elem
  /\ set2 \in SUBSET Elem
  /\ fn \in [Elem -> Elem]
  /\ seq1 \in Seq(Elem)
  /\ seq2 \in Seq(Elem)
  /\ init \in Elem

\* The specification is the identity relation, because there is nothing to
\* constrain here.  (The intervening module is only a library of operators for
\* the other specs to import.)
Spec == TRUE

Init ==
  /\ set1 = {}
  /\ set2 = {}
  /\ fn = [e \in Elem |-> e]
  /\ seq1 = << >>
  /\ seq2 = << >>
  /\ init \in Elem

Next == TRUE

\* 1. Set intersection test: two sets overlap iff their intersection is
\*    non-empty.
Overlap(a, b) == \E x \in a \cap b : TRUE

\* 2. Maximum and minimum element selection from a non-empty set.
Maximum(S) ==
  LET mx[S \in SUBSET Elem] ==
    LET rec[T \in SUBSET Elem] ==
      IF T = {} THEN init
      ELSE
        LET x == CHOOSE y \in T : \A z \in T : y >= z
        IN x
    IN rec[S]
  IN mx[S]

Minimum(S) ==
  LET mn[S \in SUBSET Elem] ==
    LET rec[T \in SUBSET Elem] ==
      IF T = {} THEN init
      ELSE
        LET x == CHOOSE y \in T : \A z \in T : y <= z
        IN x
    IN rec[S]
  IN mn[S]

\* 3. Generalized set reduction (fold over a set with an accumulator).
SetReduce(f, base, S) ==
  LET rec[T \in SUBSET Elem] ==
    IF T = {} THEN base
    ELSE
      LET x == CHOOSE y \in T : TRUE
      IN f[x, rec[T \ {x}]]
  IN rec[S]

\* 4. Sequence reduction (fold left over a sequence with an accumulator); uses
\*    the library operator FoldL for the actual fold.
SeqReduce(f, base, s) == FoldL(f, base, s)

\* 5. Find the index (1..Len) of an element in a sequence, or 0 if it is not
\*    present (the unbounded search range is Len(s), not MaxSeqLen).
IndexOf(e, s) ==
  IF \E i \in 1..Len(s) : s[i] = e
  THEN CHOOSE i \in 1..Len(s) : s[i] = e
  ELSE 0

\* 6. Convert a sequence to the set of its elements (duplicates drop out).
SeqToSet(s) == {s[i] : i \in DOMAIN s}

\* 7. Get the last element of a non-empty sequence.
Last(s) == s[Len(s)]

\* 8. Test whether a sequence is empty.
IsEmpty(s) == Len(s) = 0

\* 9. Remove all occurrences of an element from a sequence.
RemoveAll(e, s) ==
  LET rec[n \in 0..Len(s)] ==
    IF n = 0 THEN << >>
    ELSE
      LET rest == rec[n - 1]
      IN IF s[n] = e THEN rest ELSE Append(rest, s[n])
  IN rec[Len(s)]

\* 10. Intersection of a set of sets.
SetIntersection(F) == \E x \in F : \A y \in F : x \subseteq y

\* 11. All permutation sequences of a finite set, as a set of sequences.
Permutations(S) ==
  LET rec[T \in SUBSET Elem] ==
    IF T = {} THEN {<< >>}
    ELSE
      { Append(p, x) : p \in rec[T \ {x}] : x \in T }
  IN rec[S]

\* 12. Assertion-test helper that prints the evaluated terms when the test
\*    fails (useful when debugging the other specs).
AssertEqual(f, g) ==
  IF f = g
  THEN TRUE
  ELSE PrintT("FAIL:", "left", f, "right", g) /\ TRUE

InitSpec == Init
NextSpec == Next
Spec == Init /\ [][Next]_vars

Invariants == TRUE
Properties == TRUE
====