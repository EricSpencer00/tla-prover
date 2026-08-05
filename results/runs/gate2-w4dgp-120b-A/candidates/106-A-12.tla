---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS MaxSize

ASSUME MaxSize \in Nat

\* Set intersection: true iff the two sets share at least one element.
INTERSECT(A, B) == \E a \in A : a \in B

\* Greedy reduction of a set: the maximum element, or a default if the set is empty.
SETMAX(S) == LET f[T \in SUBSET S] ==
                 IF T = {} THEN 0
                 ELSE LET a \in T == CHOOSE x \in T : \A y \in T : x >= y
                      IN a
             IN f[S]

\* Greedy reduction of a set: the minimum element, or a default if the set is empty.
SETMIN(S) == LET f[T \in SUBSET S] ==
                 IF T = {} THEN 0
                 ELSE LET a \in T == CHOOSE x \in T : \A y \in T : x <= y
                      IN a
             IN f[S]

\* Generalized reduction of a set with a binary accumulator.
SETREDUCE(S, f, zero) ==
    LET g[T \in SUBSET S] ==
         IF T = {} THEN zero
         ELSE LET x \in T == CHOOSE y \in T : TRUE
                  rest == g[T \ {x}]
              IN f[x, rest]
    IN g[S]

\* Generalized reduction of a sequence with a binary accumulator.
SEQREDUCE(S, f, zero) == FoldSeq(f, zero, S)

\* Find the index of a value inside a sequence (zero if not present).
INDEXOF(S, val) ==
    LET f[i \in 1..Len(S)] ==
         IF S[i] = val THEN i
         ELSE IF i = Len(S) THEN 0
         ELSE f[i + 1]
    IN f[1]

\* Convert a sequence into the set of its elements.
SEQ2SET(S) ==
    LET f[i \in 0..Len(S)] ==
         IF i = 0 THEN {}
         ELSE f[i - 1] \cup {S[i]}
    IN f[Len(S)]

\* Return the last element of a sequence; zero if empty.
LASTSEQ(S) == IF S = <<>> THEN 0 ELSE S[Len(S)]

SEQEMPTY(S) == S = <<>>

\* Drop all occurrences of a value from a sequence.
SEQDROP(S, val) ==
    LET f[i \in 0..Len(S)] ==
         IF i = 0 THEN <<>>
         ELSE IF S[i] = val THEN f[i - 1]
         ELSE Append(f[i - 1], S[i])
    IN f[Len(S)]

\* Intersection of a set of sets.
SETINTERSECTION(S) ==
    LET g[T \in SUBSET S] ==
         IF T = {} THEN {}
         ELSE LET x \in T == CHOOSE y \in T : TRUE
                  rest == g[T \ {x}]
              IN x \cap rest
    IN g[S]

\* List all permutations of a set of low cardinality using recursion and concatenation.
PERMUTATIONS(S) ==
    LET f[T \in SUBSET S] ==
         IF T = {} THEN {<<>>}
         ELSE LET x \in T == CHOOSE y \in T : TRUE
                  rest == f[T \ {x}]
                  g[s \in rest] == Append(s, <<x>>)
              IN g[S]
    IN f[S]

\* Test helper that prints the failed assertion before returning FALSE.
ASSERT(pred, msg) == IF pred THEN TRUE ELSE (Print(msg); FALSE)

====