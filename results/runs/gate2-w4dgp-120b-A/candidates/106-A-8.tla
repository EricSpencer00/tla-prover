---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Set intersection test: two sets overlap iff they share at least one element.
Intersect(a, b) == \E x \in a : x \in b

\* Maximum element in a non-empty finite set.
Max(a) == CHOOSE m \in a : \A x \in a : x <= m

\* Minimum element in a non-empty finite set.
Min(a) == CHOOSE m \in a : \A x \in a : m <= x

\* Generalized set reduction (fold): apply binary function f over the set's
\* elements, threading an accumulator of type ft. The order of traversal over
\* a set is nondeterministic, so the reduction must be order-independent to
\* be well-defined for all traversals.
ReduceSet(a, init, f) ==
  LET fold[T \in SUBSET a] ==
        IF T = {} THEN init
        ELSE \E x \in T : f(x, fold[T \ {x}])
  IN fold[a]

\* Generalized sequence reduction (fold): apply binary function f over the
\* sequence from head to tail, threading an accumulator of type ft.
RECURSIVE FoldSeq(_:Seq(ft), _:ft, _: ft \X ft -> ft)
FoldSeq(s, init, f) ==
  IF s = <<>> THEN init
  ELSE f(Head(s), FoldSeq(Tail(s), init, f))

\* Find the index of element e in sequence s (1-based, or 0 if absent).
Index(s, e) == CHOOSE i \in 1..Len(s) : s[i] = e

\* Convert a sequence to the set of its elements (ignores order, drops dupes).
SeqToSet(s) == {s[i] : i \in 1..Len(s)}

\* The last element of a non-empty sequence.
LastElt(s) == s[Len(s)]

\* Whether a sequence is empty.
Empty(s) == Len(s) = 0

\* Remove all occurrences of element e from sequence s.
RemoveAll(s, e) ==
  IF s = <<>> THEN <<>>
  ELSE IF Head(s) = e THEN RemoveAll(Tail(s), e)
  ELSE <<Head(s)>> \o RemoveAll(Tail(s), e)

\* Intersection of a set of sets: elements common to every member set.
IntersectionOf(S) == {x \in UNION S : \A t \in S : x \in t}

\* Generate all permutation sequences of a finite set of elements (nondeterministic).
Permutations(s) ==
  LET choose[T \in SUBSET s] ==
        IF T = {} THEN {<<>>}
        ELSE UNION {<<y>> \o q : y \in T, q \in choose[T \ {y}]}
  IN choose[s]

\* Test helper: assert p, and emit a diagnostic string if it fails, so the
\* counterexample report shows why the test went wrong.
Assert(p, msg) == IF p THEN TRUE ELSE Print(msg) /\ FALSE

====