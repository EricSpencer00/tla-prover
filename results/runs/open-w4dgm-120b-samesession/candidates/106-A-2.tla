---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxSeq

\* Returns TRUE iff the two sets overlap.
SetOverlap(A, B) == \/ \E x \in A : x \in B
                  \/ \E x \in B : x \in A

\* Selects the greatest element in a non-empty set.
MaxElem(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN CHOOSE x \in S : TRUE
        ELSE LET x == CHOOSE y \in T : TRUE
                 mx == f[T \ {x}]
             IN IF x > mx THEN x ELSE mx
  IN f[S]

\* Selects the least element in a non-empty set.
MinElem(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN CHOOSE x \in S : TRUE
        ELSE LET x == CHOOSE y \in T : TRUE
                 mn == f[T \ {x}]
             IN IF x < mn THEN x ELSE mn
  IN f[S]

\* Generalized reduction over a set, with an accumulator.
SetReduce(f, S, init) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == g[T \ {x}]
             IN f[x, rest]
  IN g[S]

\* Reduction over a sequence, folding from the left using the library operator.
SeqReduce(f, seq, init) == ReduceSeq(seq, f, init)

\* Returns the index of e in seq, or 0 if e is absent.
SeqIndex(seq, e) ==
  LET f[i \in 1..Len(seq)] ==
        IF seq[i] = e THEN i ELSE IF i = Len(seq) THEN 0 ELSE f[i + 1]
  IN f[1]

\* Returns the set of all elements appearing in seq.
SeqSet(seq) ==
  LET f[i \in 1..Len(seq)] ==
        IF i = Len(seq) THEN {seq[i]}
        ELSE {seq[i]} \cup f[i + 1]
  IN IF seq = <<>> THEN {} ELSE f[1]

\* Returns the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* True if seq is empty.
SeqIsEmpty(seq) == Len(seq) = 0

\* Returns seq with all occurrences of e removed.
SeqRemoveAll(seq, e) ==
  SELECTOR L \in SUBSET seq :
    /\ \A i \in 1..Cardinality(L) : seq[i] \notin L
    /\ Cardinality(L) = Len(seq) - Cardinality({i \in 1..Len(seq) : seq[i] = e})

\* Returns the intersection of the non-empty set of non-empty sets in S.
SetIntersect(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN CHOOSE x \in S : TRUE
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == f[T \ {x}]
             IN rest \cap x
  IN f[S]

\* Generates all permutation sequences of the finite set S.
Permutations(S) ==
  { seq \in Seq(1..MaxSeq) : Cardinality({i \in 1..Len(seq) : seq[i] \in S}) = Len(seq) }

\* Test helper: asserts p and prints a diagnostic message when p is false.
Assert(p, msg) == p /\ (IF ~p THEN UNCHANGED << >> /\ Print(msg) ELSE UNCHANGED << >>)

====