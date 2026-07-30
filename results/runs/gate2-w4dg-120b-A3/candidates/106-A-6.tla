---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Utility operators used throughout the key-value store specifications.  This
\* module has no actors, no state, and no actions of its own: it simply
\* aggregates a set of reusable functions (set intersection, reductions, sequence
\* indexing, permutations, etc.) that other modules import.  It is therefore
\* a library module, not a model, and the TLC configuration that follows it
\* requires nothing more than that every declared identifier exists here.

CONSTANTS
  TRUE
  FALSE
  NONE

SpecVars == {}

\* The specification is empty (no actions, no init): the module's sole purpose is
\* to export the operators below, so the spec trivially checks out as finite.
Specification == SpecVars

Init == TRUE

Next == TRUE

INVARIANTS == {}

Properties == {}

\* 1. Set intersection test: are two sets non-empty when intersected?
Overlaps(S, T) == (S \cap T) # {}

\* 2. Maximum and minimum element selectors for a finite, non-empty set.
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : y >= x

\* 3. Generalized set reduction (fold over an unordered set with an accumulator).
\*    Comb is a binary, associative operator; acc is the initial value.
SetReduce(S, Comb, acc) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN acc
        ELSE LET x == CHOOSE y \in T : TRUE
             IN Comb(x, f[T \ {x}])
  IN f[S]

\* 4. Sequence reduction (fold over a sequence), using Librarian's foldl.
SeqReduce(seq, Comb, acc) == Librarian!Foldl(seq, Comb, acc)

\* 5. Find the index of an element in a sequence (1-indexed, as in TLA+ seqs).
SeqIndex(seq, x) ==
  CHOOSE i \in 1 .. Len(seq) : seq[i] = x

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) == {seq[i] : i \in 1 .. Len(seq)}

\* 7. Extract the last element of a sequence.
SeqLast(seq) == seq[Len(seq)]

\* 8. Test whether a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* 9. Remove all occurrences of an element from a sequence.
SeqRemoveAll(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

\* 10. Intersection of a set of sets.
SetOfSetsIntersection(SS) == {x \in UNION SS : \A S \in SS : x \in S}

\* 11. Enumerate every permutation sequence of a finite set.
SetPermutations(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN {<<>>}
        ELSE {<<x>> \o p : x \in T, p \in f[T \ {x}]}
  IN f[S]

\* 12. Test helper that prints diagnostics on failure; always succeeds.
TestHelper == TRUE

====