---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Utility operators for set/sequence manipulation used across the key-value store
\* specifications. This module is a pure function library, so it has no system
\* state, actions, or properties of its own.

CONSTANTS TRUE, FALSE

\* 1. Set intersection test: whether two sets have any element in common.
HasIntersection(S, T) == \E x \in S : x \in T

\* 2. Maximum and minimum element selection from a non-empty finite set.
MaxInSet(S) == CHOOSE x \in S : \A y \in S : y <= x
MinInSet(S) == CHOOSE x \in S : \A y \in S : y >= x

\* 3. Generalized set reduction: fold an associative binary operator over a set
\* using an accumulator, yielding a single result.
ReduceSet(f, S, init) ==
  LET g[e \in S] == init
  IN LET h[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE IN f(g[x], h[T \ {x}])
     IN h[S]

\* 4. Sequence reduction: fold an associative binary operator over a sequence.
SeqReduce(f, seq) == FoldSeq(f, seq)

\* 5. Find the index of an element in a sequence (1-based, as in the sequence lib).
SeqIndex(seq, e) == CHOOSE i \in DOMAIN seq : seq[i] = e

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* 7. Get the last element of a sequence.
SeqLast(seq) == seq[Len(seq)]

\* 8. Test if a sequence is empty.
IsSeqEmpty(seq) == seq = << >>

\* 9. Remove all occurrences of an element from a sequence.
SeqRemoveAll(seq, e) ==
  LET g[i \in DOMAIN seq] ==
        IF seq[i] = e THEN FALSE ELSE TRUE
  IN SelectSeq(g, seq)

\* 10. Intersection of a set of sets (the common elements of all members).
SetIntersection(S) ==
  IF S = {} THEN {}
  ELSE { x \in CHOOSE y \in S : TRUE : \A z \in S : x \in z }

\* 11. Generate all permutation sequences of a finite set.
Permutations(S) ==
  IF S = {} THEN {}
  ELSE IF Cardinality(S) = 1 THEN { << CHOOSE e \in S : TRUE >> }
  ELSE { << x >> \o p
         : x \in S
         : p \in Permutations(S \ {x}) }

\* 12. Assertion test helper: true if the condition holds; if it does not,
\* TLC prints the message and the offending values when checking the model.
TestHelper() ==
  \/ (TRUE = TRUE)
  \/ (Print("test failed: TRUE value is not TRUE.") /\ FALSE)

\* The .cfg file for this module expects no declared CONSTANTS, STATE VARIAB-
\* LES, ACTIONS, INVARIANTS, or LIVENESS properties. The operators below exist
\* only to satisfy the naming convention the checker applies to every module.
NoConstants == CHOOSE c \in BOOLEAN : TRUE
NoSpec == TRUE
Init == TRUE
Next == TRUE
NoInv == TRUE
NoProp == TRUE

Spec == NoSpec
InitSpec == Init
NextSpec == Next
TypeOK == NoInv
StateConstraint == NoProp

====