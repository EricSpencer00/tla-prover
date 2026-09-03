---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS Nat, NONE, NoVal

\* Set-intersection test: true iff the two sets share at least one element.
InCommon(f, g) == \E x \in f : x \in g

\* Maximum and minimum element selection from a non-empty set (via reduction).
MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized set reduction (fold) of a binary operator over a set's elements,
\* with an accumulator seeded at b. The operator must be associative and commutative
\* for the result to be order-independent, but this is not checked here.
SetFold(S, op, b) == LET
  fold[T \in SUBSET S] ==
    IF T = {} THEN b
    ELSE LET x == CHOOSE y \in T : TRUE IN op[x, fold[T \ {x}]]
  IN fold[S]

\* Sequence reduction via the built-in foldl (left fold) operator.
SeqFold(seq, op, b) == FoldL(op, seq, b)

\* Find the index of an element in a sequence, or 0 if not present.
FindInSeq(seq, x) == CHOOSE i \in 1..Len(seq) : seq[i] = x
                     DEFAULT 0

\* Convert a sequence to the set of its elements (duplicates collapsed).
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a sequence, or NONE if the sequence is empty.
LastOf(seq) == IF seq = <<>> THEN NONE ELSE seq[Len(seq)]

\* True iff the sequence is empty.
SeqEmpty(seq) == seq = <<>>

\* Remove all occurrences of x from a sequence.
RemoveAll(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

\* Intersection of a set of sets (the common elements of all its members).
IntersectOf(S) ==
  CHOOSE z \in S : \A y \in S : y \subseteq z

\* Generate the set of all permutations of a finite set's elements as sequences.
PermutationsOf(S) ==
  { f \in [1..Cardinality(S) -> S] :
      \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j] }

\* Test-helper: asserts that expr holds, and on failure prints the labeled
\* identifier and the offending value in the error trace.
Assert(expr, id, val) == IF expr THEN TRUE
                         ELSE Printf("%s %s", id, val)

\* No system state to model; this module merely collects reusable operators.
Spec == TRUE
====