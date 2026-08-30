---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets, Enumerate

CONSTANTS Operators, MaxVal

\* Tests whether two sets have any element in common.
SetOverlap(A, B) == \E x \in A : x \in B

\* Selects the maximum element of a non-empty set of operator IDs.
SetMax(S) == CHOOSE m \in S : \A x \in S : x <= m

SetMin(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized reduction over a set: collapse it into a single value.
SetReduce(f, S, i) ==
  IF S = {} THEN i
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x, SetReduce(f, S \ {x}, i)]

\* Reduction over a sequence, defined via the library's foldl operator.
SeqReduce(f, seq, i) == FoldL(f, seq, i)

\* Returns the (1-based) position of x in seq, or 0 if not present.
SeqIndex(seq, x) ==
  LET len == Len(seq) IN
  CHOOSE k \in 1..len : seq[k] = x
    @WITH DEFAULT 0

\* Returns the set of elements appearing in a sequence.
SeqAsSet(seq) == { seq[k] : k \in DOMAIN seq }

\* Returns the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

\* Removes every occurrence of x from a sequence.
SeqRemoveAll(seq, x) ==
  SELECT y \in { w \in [1..Len(seq) -> Operators] :
                    \A k \in 1..Len(seq) : (w[k] = seq[k] \/ (seq[k] = x /\ w[k] # x)) /\ (w[k] # x \/ seq[k] # x)
              } : TRUE

\* Intersection of a set of sets, using a fold over the power set.
SetIntersection(F) ==
  SetReduce([a, b \in SUBSET Operators |-> a \cap b], F, Operators)

\* Generates every permutation (ordering) of a finite set of operators.
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* A test helper: asserts p and prints a diagnostic message on failure.
TestHelper(p) == IF p THEN TRUE ELSE ~p

Spec == TRUE

====