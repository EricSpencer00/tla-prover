---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS NoSentinel

\* Utility operators used across the key-value store specifications:
\*  1. SetIntersect  : test whether two sets overlap
\*  2. SetMax / SetMin: maximum and minimum element selection from a set
\*  3. SetReduce      : generalized set reduction (fold over a set)
\*  4. SeqReduce      : sequence reduction using a fold operator
\*  5. IndexOf        : find the index of an element in a sequence
\*  6. AsSet          : convert a sequence to the set of its elements
\*  7. LastOf         : the last element of a sequence
\*  8. IsEmpty        : test if a sequence is empty
\*  9. RemoveAll      : remove all occurrences of an element from a seq
\* 10. Intersections : compute the intersection of a set of sets
\* 11. Permutations   : generate all permutations of a finite set
\* 12. TestHelper     : test helper that prints diagnostics on failure
=============================================================================