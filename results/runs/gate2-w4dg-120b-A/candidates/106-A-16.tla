---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Constants: each operator's parameter names and the overall operator set.
CONSTANTS
  a, b,
  set1, set2,
  seq1, seq2,
  f, g,
  e,
  S

\* No system state: the spec is simply the conjunction of the operators.
SPECIFICATION == TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == TRUE

PROPERTIES == TRUE

\* Operator 1: intersection test -- TRUE iff two sets overlap.
Intersects(sa, sb) == \E x \in sa : x \in sb

\* Operator 2: maximum element of a finite set of naturals.
MaxOf(S) == LET f[T \in SUBSET S] ==
                 IF T = {} THEN 0
                 ELSE LET x == CHOOSE y \in T : TRUE
                          T1 == T \ {x}
                      IN IF T1 = {} THEN x ELSE IF x > f[T1] THEN x ELSE f[T1]
            IN f[S]

\* Operator 2(b): minimum element of a finite set of naturals.
MinOf(S) == LET f[T \in SUBSET S] ==
                 IF T = {} THEN 0
                 ELSE LET x == CHOOSE y \in T : TRUE
                          T1 == T \ {x}
                      IN IF T1 = {} THEN x ELSE IF x < f[T1] THEN x ELSE f[T1]
            IN f[S]

\* Operator 3: generalized fold/reduce over a set.
SetFold(S, f, init) == LET g[T \in SUBSET S] ==
                           IF T = {} THEN init
                           ELSE LET x == CHOOSE y \in T : TRUE
                                    T1 == T \ {x}
                                IN f(x, g[T1])
                       IN g[S]

\* Operator 4: fold/reduce over a sequence, using the library operator.
SeqFold(seq, init, f) == Reduce(f, init, seq)

\* Operator 5: index of an element in a sequence (0 if not present).
IndexOf(seq, e) ==
  LET f[T \in SUBSET DOMAIN seq] ==
       IF T = {} THEN 0
       ELSE LET i == CHOOSE j \in T : TRUE
                T1 == T \ {i}
            IN IF seq[i] = e THEN i ELSE f[T1]
  IN f[DOMAIN seq]

\* Operator 6: convert a sequence to the set of its elements.
SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

\* Operator 7: the last element of a sequence.
Last(seq) == IF seq = <<>> THEN 0 ELSE seq[Len(seq)]

\* Operator 8: test whether a sequence is empty.
IsEmpty(seq) == seq = <<>>

\* Operator 9: remove all occurrences of an element from a sequence.
RemoveAll(seq, e) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

\* Operator 10: intersection of a set of sets.
SetIntersection(T) ==
  LET f[U \in SUBSET T] ==
       IF U = {} THEN {}
       ELSE LET x == CHOOSE y \in U : TRUE
                R == f[U \ {x}]
            IN IF R = {} THEN x ELSE Intersect(x, R)
  IN f[T]

\* Operator 11: generate all permutation sequences of a finite set.
PermutationsOf(S) ==
  LET f[T \in SUBSET S] ==
       IF T = {} THEN {<<>>}
       ELSE LET x == CHOOSE y \in T : TRUE
                rest == f[T \ {x}]
                prepend(y, seq) == <<y>> \o seq
                seqs == {prepend(x, s) : s \in rest}
            IN seqs
  IN f[S]

\* Operator 12: test helper that prints diagnostics on failure.
AssertTrue(c) == IF c THEN TRUE ELSE UNCHANGED c

====