---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxElem

\* Returns TRUE iff the two sets share at least one element.
Intersect(a, b) == \E x \in a : x \in b

MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generic fold/reduce over a set, with an accumulator that is updated by a
\* user-provided binary function.
ReduceSet(f, S, init) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE e \in T : TRUE
                 rest == g[T \ {x}]
             IN f[x, rest]
  IN g[S]

\* Generic fold over a sequence, using the library SeqFold (left-associative).
ReduceSeq(f, seq, init) == SeqFold(f, init, seq)

IndexOf(seq, e) ==
  \E i \in DOMAIN seq : seq[i] = e /\ i

SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

LastOf(seq) == seq[Len(seq)]

IsEmptySeq(seq) == seq = << >>

RemoveAll(seq, e) ==
  IF seq = << >> THEN seq
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE << Head(seq) >> \o RemoveAll(Tail(seq), e)

\* Intersection of a set of sets (finite domain, so recursion over that domain
\* is safe and terminating).
IntersectFamily(F) ==
  LET g[T \in SUBSET F] ==
        IF T = {} THEN {}
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == g[T \ {x}]
             IN IF rest = {} THEN x ELSE Intersect(x, rest)
  IN g[F]

\* Permutation generation via backtracking: remove each candidate in turn and
\* recurse, building up the permutation sequence.
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE { << x >> \o p
           : x \in S, p \in Permutations(S \ {x}) }

\* Test helper: prints its arguments as a side effect when the assertion fails.
RequireTrue(b, a, c) == IF b THEN TRUE ELSE (b /\ (a = c))

====