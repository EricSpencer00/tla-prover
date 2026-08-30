---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS

Spec == "Specification"
Init == "Init"
Next == "Next"
Invs == "INVARIANTS"
Props == "PROPERTIES"

\* set intersection test (whether two sets overlap)
Intersects(A, B) == \E x \in A : x \in B

\* maximum element of a non-empty set
MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m

\* minimum element of a non-empty set
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* generalized set reduction: fold a binary function over a set with an
\* accumulator, applying the function to each element in arbitrary order
SetReduce(f, S, init) ==
  LET Rec(T, a) ==
        IF T = {} THEN a
        ELSE \E x \in T : Rec(T \ {x}, f[a, x])
  IN Rec(S, init)

\* sequence reduction: fold a binary function over a sequence with an
\* accumulator, applying the function left-to-right over the sequence
SeqReduce(f, s, init) == FoldL(f, s, init)

\* return the 1-based index of an element in a sequence, or 0 if not present
IndexOf(s, x) == Head({ i \in 1..Len(s) : s[i] = x } \cup {0})

\* convert a sequence to the set of its elements
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* retrieve the last element of a non-empty sequence
LastOf(s) == s[Len(s)]

\* test whether a sequence is empty
SeqEmpty(s) == Len(s) = 0

\* remove all occurrences of an element from a sequence
SeqRemoveAll(s, x) ==
  LET Rec(i, acc) ==
        IF i > Len(s) THEN acc
        ELSE IF s[i] = x THEN Rec(i + 1, acc)
        ELSE Rec(i + 1, Append(acc, s[i]))
  IN Rec(1, << >>)

\* compute the intersection of a set of sets
InterAll(sets) ==
  LET Rec(T, acc) ==
        IF T = {} THEN acc
        ELSE \E x \in T : Rec(T \ {x}, Intersects(acc, x) /\ x)
  IN Rec(sets, TRUE)

\* generate every permutation sequence of a finite set
Permutations(S) ==
  LET Rec(T) ==
        IF T = {} THEN { << >> }
        ELSE { Append(p, x) : x \in T, p \in Rec(T \ {x}) }
  IN Rec(S)

\* test helper: assert a condition, printing the message on failure
Test(msg, cond) == IF cond THEN TRUE ELSE (msg /\ FALSE)

====