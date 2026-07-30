---- MODULE Util ----
EXTENDS Integer, FiniteSets, Sequences

CONSTANTS UNICODE

\* Utility library used by the key-value store specifications.  No actors,
\* no state, just pure functional operators.
\* The module's own SPECIFICATION/INIT/etc. are dummies that satisfy the
\* (empty) set of identifiers required by the reference .cfg.
\* Each operator below is named exactly as described above.

ASSUME UNICODE \in STRING

\* Required identifiers that the .cfg expects; the spec itself has no
\* dynamics, so the operators simply return TRUE.
TrueSpec == TRUE

Spec == TrueSpec
Init == TrueSpec
Next == TrueSpec
SpecInv == TrueSpec
SpecProp == TrueSpec

\* 1. Set intersection test: whether the two sets overlap.
Intersects(A, B) == \E x \in A : x \in B

\* 2a. Maximum element selection from a set.
MaxSet(S) == CHOOSE x \in S : \A y \in S : y <= x

\* 2b. Minimum element selection from a set.
MinSet(S) == CHOOSE x \in S : \A y \in S : y >= x

\* 3. Generalized set reduction: fold a binary operator over a set with an
\*    accumulator, order-free because the operator is assumed commutative.
SetReduce(f, S, init) ==
  LET vals == {s : s \in S}
  IN IF vals = {} THEN init
     ELSE LET x == CHOOSE y \in vals : TRUE
          IN f(x, SetReduce(f, vals \ {x}, init))

\* 4. Sequence reduction: fold a binary operator over a sequence, left to
\*    right -- here implemented via the library FoldSeq.
SeqReduce(f, seq, init) == FoldSeq(f, init, seq)

\* 5. Find the index of an element in a sequence.
IndexOf(seq, e) == CHOOSE i \in DOMAIN seq : seq[i] = e

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

\* 7. Last element of a sequence.
SeqLast(seq) == seq[Len(seq)]

\* 8. Test whether a sequence is empty.
SeqEmpty(seq) == seq = << >>

\* 9. Remove all occurrences of an element from a sequence.
RemoveAll(seq, e) ==
  LET f(acc, x) == IF x = e THEN acc ELSE Append(acc, x)
  IN SeqReduce(f, seq, << >>)

\* 10. Intersection of a set of sets.
SetOfSetsIntersect(T) ==
  IF T = {} THEN {}
  ELSE LET S == CHOOSE t \in T : TRUE
       IN S \cap SetOfSetsIntersect(T \ {S})

\* 11. Generate all permutation sequences of a finite set.
AllPermutations(S) ==
  IF S = {} THEN {<< >>}
  ELSE UNION { [x] \o seq : x \in S, seq \in AllPermutations(S \ {x}) }

\* 12. Test-helper that throws a diagnostic message on failure; in a real
\*    spec it would be used inside an ASSERT.
CheckDiag(cond, msg) == IF cond THEN TRUE ELSE UNICODE

====