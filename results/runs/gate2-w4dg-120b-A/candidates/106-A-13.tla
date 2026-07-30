---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

\* Set-intersection test: two sets overlap iff their intersection is non-empty.
INTERSECTION(a, b) == Cardinality(a \cap b) > 0

\* Pick the maximum element from a non-empty set of naturals.
MAX(e) == LET f[x \in e] == \E y \in e : y >= x /\ \A z \in e : z <= y
          IN f[CHOOSE x \in e : TRUE]

\* Pick the minimum element from a non-empty set of naturals.
MIN(e) == LET f[x \in e] == \E y \in e : y <= x /\ \A z \in e : z >= y
          IN f[CHOOSE x \in e : TRUE]

\* Generalized reduction (fold) over a set.
REDUCE(f, z, S) == IF S = {} THEN z
                   ELSE LET x == CHOOSE y \in S : TRUE
                        IN REDUCE(f, f(z, x), S \ {x})

\* Generalized reduction (fold) over a sequence using the library operator.
REDUCES(f, z, s) == FoldSeq(f, z, s)

\* Find the index of an element in a sequence (1-indexed, returning 0 on failure).
INDEXOF(s, v) == IF \E i \in DOMAIN s : s[i] = v
                 THEN CHOOSE i \in DOMAIN s : s[i] = v
                 ELSE 0

\* Turn a sequence into the set of its elements.
SEQ2SET(s) == { s[i] : i \in DOMAIN s }

\* Get the last element of a non-empty sequence.
LAST(s) == s[Len(s)]

\* Test whether a sequence is empty.
EMPTY(s) == Len(s) = 0

\* Remove all occurrences of a value from a sequence.
REMOVEALL(s, v) == [i \in 1..Len(s) |-> s[i] : s[i] # v]

\* Intersection of a set of sets (only for non-empty families).
INTERSECTF(f) == LET x == CHOOSE y \in f : TRUE
                IN \A z \in f : x \subseteq z

\* Generate all permutations of a set as sequences (only for sets with size <= N).
PERMUTATIONS(e) == IF Cardinality(e) > N
                   THEN {}
                   ELSE SELECT s \in [1..Cardinality(e) -> e] :
                        Cardinality(SEQ2SET(s)) = Cardinality(e)

\* Test helper that prints the expression on failure.
HYPEREQ(x, y) == x = y /\ (IF x = y THEN TRUE ELSE Print("FAIL: expected ", y, " got ", x))

\* The configuration's "no identifiers required" clause is not a mistake: this
\* module has no model-level operators of its own, so the SPECIFICATION, INIT,
\* NEXT, INVARIANTS, and PROPERTIES operators below are each defined as a
\* no-op identity only so that the .cfg can name them.

SPECIFICATION == "Specification identity placeholder"
INIT == "Init identity placeholder"
NEXT == "Next identity placeholder"
INVARIANTS == "Invariants identity placeholder"
PROPERTIES == "Properties identity placeholder"

====