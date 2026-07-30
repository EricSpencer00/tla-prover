---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Permuted

\* Intersection test: two sets share at least one element.
CONSTANTS Intersects
Intersects(a, b) == \E x \in a : x \in b

\* Max and min element selection from a set.
CONSTANTS MaxElem, MinElem
MaxElem(S, f) == LET g[T \in SUBSET S] ==
                     IF T = {} THEN -1
                     ELSE LET x == CHOOSE y \in T : TRUE
                          IN IF T = {x} THEN f[x] ELSE Max(f[x], g[T \ {x}])
                 IN g[S]
MinElem(S, f) == LET g[T \in SUBSET S] ==
                     IF T = {} THEN 7
                     ELSE LET x == CHOOSE y \in T : TRUE
                          IN IF T = {x} THEN f[x] ELSE Min(f[x], g[T \ {x}])
                 IN g[S]

\* Generalized set reduction (fold over a set with an accumulator).
CONSTANTS FoldrSet
FoldrSet(f, S, b) ==
  LET g[T \in SUBSET S] ==
       IF T = {} THEN b
       ELSE LET x == CHOOSE y \in T : TRUE
            IN f[x, g[T \ {x}]]
  IN g[S]

\* Sequence reduction (fold over a sequence with an accumulator), via library FoldL.
CONSTANTS FoldrSeq
FoldrSeq(f, s, b) == FoldL(f, b, s)

\* Find the index of an element in a sequence.
CONSTANTS FindIndex
FindIndex(s, y) ==
  LET g[i \in 0..Len(s)] ==
       IF i = Len(s) THEN -1
       ELSE IF s[i + 1] = y THEN i + 1 ELSE g[i + 1]
  IN g[0]

\* Convert a sequence to the set of its elements.
CONSTANTS ToSet
ToSet(s) == {s[i] : i \in 1..Len(s)}

\* The last element of a sequence.
CONSTANTS LastOf
LastOf(s) == IF s = <<>> THEN -1 ELSE s[Len(s)]

\* Predicate: a sequence is empty.
CONSTANTS IsEmpty
IsEmpty(s) == s = <<>>

\* Remove all occurrences of an element from a sequence.
CONSTANTS RemoveAll
RemoveAll(s, y) ==
  IF s = <<>> THEN <<>>
  ELSE IF Head(s) = y THEN RemoveAll(Tail(s), y)
  ELSE <<Head(s)>> \o RemoveAll(Tail(s), y)

\* Intersection of a set of sets.
CONSTANTS IntersectSet
IntersectSet(G) ==
  LET f[T \in SUBSET G] ==
       IF T = {} THEN {}
       ELSE LET x == CHOOSE y \in T : TRUE
            IN IF T = {x} THEN x ELSE Intersects(x, f[T \ {x}])
  IN f[G]

\* Generate all permutation sequences of a finite set.
CONSTANTS Permutations
Permutations(S) ==
  IF S = {} THEN {<<>>}
  ELSE {<<x>> \o p : x \in S, p \in Permutations(S \ {x})}

\* Test helper: write an assertion that prints diagnostic information on failure.
CONSTANTS TestIff
TestIff(p, q) == p <=> q

====