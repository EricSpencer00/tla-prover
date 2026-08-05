---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS

VARIABLES

vars == {}

Init == vars = {}
Next == UNCHANGED vars

\* Intersects(a, b) holds iff the two sets a and b share at least one element.
Intersects(a, b) == \E x \in a : x \in b

\* MaxIn(e) returns the element in set e that is greater than every other.
MaxIn(e) == CHOOSE x \in e : \A y \in e : y <= x

\* MinIn(e) returns the element in set e that is smaller than every other.
MinIn(e) == CHOOSE x \in e : \A y \in e : x <= y

\* SetReduce(f, e, zero) folds the commutative function f over the set e, starting
\* at zero; the order of application is nondeterministic, so the reduction must be
\* order-independent for the result to be well defined.
SetReduce(f, e, zero) ==
  IF e = {}
  THEN zero
  ELSE LET x == CHOOSE y \in e : TRUE IN f(x, SetReduce(f, e \ {x}, zero))

\* SeqReduce(f, s, zero) folds the function f over the sequence s, left to right.
SeqReduce(f, s, zero) ==
  LET g[T \in Seq(Tuple)] ==
        IF T = <<>> THEN zero
        ELSE LET x == Head(T) IN f(x, g(Tail(T)))
  IN g(s)

\* IndexOf(s, x) returns the smallest index i such that s[i] = x, or 0 if x is absent.
IndexOf(s, x) == CHOOSE i \in 1..Len(s) : s[i] = x

\* SetOf(s) converts a sequence to the set of its elements.
SetOf(s) == { s[i] : i \in 1..Len(s) }

\* LastSeq(s) returns the last element of a non-empty sequence.
LastSeq(s) == IF s = <<>> THEN CHOOSE x \in {} : TRUE ELSE s[Len(s)]

\* IsSeqEmpty(s) is true exactly when s has no elements.
IsSeqEmpty(s) == s = <<>>

\* RemoveAll(s, x) strips every occurrence of element x from sequence s.
RemoveAll(s, x) == [ i \in 1..(Len(s) - Cardinality({j \in 1..Len(s) : s[j] = x}))
                      |-> s[ IF i < CHOOSE j \in 1..Len(s) : s[j] = x THEN i ELSE i + 1 ] ]

\* SetOfSetsIntersection(sets) folds intersection over a set of sets, starting with
\* the universal set of the domain (so it only shrinks).
SetOfSetsIntersection(sets) ==
  SetReduce([a, b \in SUBSET Nat |-> a \cap b], sets, Nat)

\* AllPermutations(e) returns the set of all sequences that are permutations of e.
AllPermutations(e) ==
  IF e = {}
  THEN { <<>> }
  ELSE { s \in Seq(e) : SetOf(s) = e \wedge Len(s) = Cardinality(e) }

\* ExpectEqual is used in an ASSERT to print both sides on failure.
ExpectEqual(a, b) == (a = b) /\ TRUE

====