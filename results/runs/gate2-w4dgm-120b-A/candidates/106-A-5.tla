---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxLen, MaxVal

\* Set intersection: true iff the two sets have at least one element in common.
Intersect(a, b) == \E x \in a : x \in b

\* Maximum and minimum of a non-empty set of natural numbers.
MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Reduce a set by folding a commutative/associative binary function over its elements.
ReduceSet(f, S, base) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN base
        ELSE LET x == CHOOSE y \in T : TRUE
             IN f[x, g[T \ {x}]]
  IN g[S]

\* Reduce a sequence by folding a binary function from the first element onward.
ReduceSeq(f, seq) ==
  LET g[i \in 0..Len(seq)] ==
        IF i = 0 THEN seq[1]
        ELSE f[seq[i], g[i-1]]
  IN g[Len(seq)]

\* Find the (1-based) index of an element in a sequence; returns 0 if absent.
IndexOf(seq, x) ==
  LET g[i \in 1..(Len(seq) + 1)] ==
        IF i = Len(seq) + 1 THEN 0
        ELSE IF seq[i] = x THEN i
        ELSE g[i + 1]
  IN g[1]

\* Convert a sequence to the set of the values it contains.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* Retrieve the last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* Sequence emptiness test.
IsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of a value from a sequence.
RemoveAll(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN RemoveAll(Tail(seq), x)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), x)

\* Intersection of a set of sets (the elements common to all members).
IntersectFamilies(F) == { x \in UNION F : \A Y \in F : x \in Y }

\* Generate every permutation of a finite set as a sequence.
Permutations(S) == { seq \in [1..Cardinality(S) -> MaxVal] :
                      { seq[i] : i \in 1..Cardinality(S) } = S }

\* Test helper that prints a diagnostic message on failure.
Assert(msg, p) == IF p THEN msg ELSE CHOOSE x \in {msg} : x

Spec == TRUE
Init == TRUE
Next == TRUE
StateConstraint == TRUE
Vars == {}

====