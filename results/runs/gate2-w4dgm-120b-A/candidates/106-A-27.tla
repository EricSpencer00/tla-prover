---- MODULE Util ----
EXTENDS Integers, Sequences

CONSTANTS MaxSet, MaxSeq, MaxPerms

\* Set-intersection test: TRUE iff the two sets have any common element.
Intersect(A, B) == \E x \in A : x \in B

\* Fold a binary function over a set, carrying an accumulator.
FoldSet(f, S, z) == IF S = {} THEN z
                    ELSE LET x == CHOOSE y \in S : TRUE
                         IN f[x, FoldSet(f, S \ {x}, z)]

\* Fold a binary function over a sequence, using the library's \inseq fold.
FoldSeq(f, s, z) == \E g \in [1..Len(s) -> S \X S] :
                      g[1] = <<s[1], z>> /\ \A i \in 2..Len(s) : g[i] = <<s[i], f[g[i-1]]>>
                      /\ f[g[Len(s)]] = g[Len(s+1)]

\* Index of an element in a sequence, or -1 if not present.
IndexOf(s, e) == IF \E i \in 1..Len(s) : s[i] = e
                 THEN CHOOSE i \in 1..Len(s) : s[i] = e
                 ELSE -1

\* Convert a sequence into the set of its elements; order is discarded.
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* Returns the last element of a non-empty sequence.
Last(s) == s[Len(s)]

\* Predicate true iff the sequence is empty.
IsEmpty(s) == Len(s) = 0

\* Remove all occurrences of an element from a sequence, preserving order of the rest.
RemoveAll(s, e) == SelectSeq(s, LAMBDA x : x # e)

\* Intersection of a set of sets; folds \inset across the family.
IntersectFamily(F) == FoldSet(Intersect, F, UNCHANGED)

\* Generate, nondeterministically, a permutation sequence of a finite set's elements.
Permutations(S) ==
    \E p \in (Seq(ToSet(S)) \X 1..MaxPerms) :
        /\ Cardinality(p[1]) = Cardinality(S)
        /\ \A i \in 1..Len(p[1]) : p[1][i] \in S
        /\ \A i, j \in 1..Len(p[1]) : i # j => p[1][i] # p[1][j]

\* Test helper that yields TRUE, but prints a diagnostic message if its argument is FALSE.
Assert(c) == IF c THEN TRUE ELSE (Print("ASSERTION FAILED"); FALSE)

====