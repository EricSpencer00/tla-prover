---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Utility operators used by other specs in the KV store project.  The
\* spec as a whole has no actors, no state, and no actions: it is a
\* collection of pure functions over sets and sequences.
\* The identifier list (SPECIFICATION, INIT, NEXT, INVARIANTS,
\* PROPERTIES) is required by the reference model's .cfg even though
\* they do nothing here.

CONSTANTS MaxNat, MaxLen

VARIABLES dummy
vars == <<dummy>>

TypeOK ==
  /\ dummy \in Nat

SpecPart ==
  /\ dummy' = dummy

SPECIFICATION == SpecPart
INIT == SpecPart
NEXT == SpecPart
INVARIANTS == SpecPart
PROPERTIES == SpecPart

\* 1. Set overlap test: true iff two finite sets have a non-empty intersection.
Overlap(A, B) == \E x \in A : x \in B

\* 2. Maximum element of a non-empty finite set of naturals.
MaxOf(S) ==
  /\ S # {}
  /\ \E m \in S :
       /\ \A x \in S : x <= m
       /\ m

\* 3. Minimum element of a non-empty finite set of naturals.
MinOf(S) ==
  /\ S # {}
  /\ \E m \in S :
       /\ \A x \in S : m <= x
       /\ m

\* 4. Generalized reduction (fold) over a set, with an accumulator and a commutative operator.
SetReduce(S, op, zero) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN zero
        ELSE
          LET x == CHOOSE y \in T : TRUE
          IN op[x, f[T \ {x}]]
  IN f[S]

\* 5. Reduction over a sequence, using the library FoldSeq operator.
SeqFold(seq, f, zero) == FoldSeq(seq, f, zero)

\* 6. Index of an element in a sequence (returns zero if not present).
SeqIndex(seq, x) ==
  IF \E i \in DOMAIN seq : seq[i] = x
  THEN CHOOSE i \in DOMAIN seq : seq[i] = x
  ELSE 0

\* 7. Convert a sequence to the set of its elements.
SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

\* 8. The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* 9. Empty-sequence test.
SeqEmpty(seq) == seq = << >>

\* 10. Remove all occurrences of an element from a sequence.
SeqRemoveAll(seq, x) ==
  << seq[i] : i \in DOMAIN seq /\ seq[i] # x >>

\* 11. Intersection of a set of sets.
SetOfSetsInter(T) ==
  /\ T # {}
  /\ \E x \in UNION T :
       /\ \A s \in T : x \in s
       /\ x

\* 12. Generate all permutations of a finite set (each permutation as a
\*     sequence of length |S|).
Permutations(S) ==
  LET insertAll(s, x) == { <<x>> } \cup { <<s[i]>> @@ <<x>> : i \in 1..Len(s) } \cup { <<x>> @@ s : s \in S }
  IN IF S = {} THEN { << >> } ELSE UNION { insertAll(p, x) : x \in S : p \in Permutations(S \ {x}) }

\* 13. Test helper: always true, but prints a diagnostic message on its failure.
TestHelper(msg) == TRUE

====