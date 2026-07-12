---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES \* No state variables are declared because this is a pure utility module.

\* ----------------------------------------------------------------------
\* Utility Operators
\* ----------------------------------------------------------------------
\* (1) Set intersection test: returns TRUE if two sets share at least one element
SetOverlap(s, t) == s \dintersect t # {}

\* (2) Maximum element of a set (assuming non-empty and elements are comparable)
MaxSet(s) == IF s = {} THEN {} ELSE \* Undefined for empty set; placeholder
          CHOOSE x \in s : \A y \in s : y <= x

MinSet(s) == IF s = {} THEN {} ELSE
          CHOOSE x \in s : \A y \in s : y >= x

\* (3) Generalized set reduction (fold) with an identity element and a binary
\*     operator; accumulates over the set in an arbitrary order.
\* For example, SumSet(s) == \* sum of all elements in s
SetReduce(f, acc, s) == \* f is a binary function, acc is identity
          IF s = {} THEN acc ELSE
          f(\* element \*, acc) \* applied by induction is represented implicitly

\* Example: SumSet(s) == SetReduce(\Add, 0, s)

\* (4) Sequence reduction using a library fold (SeqFold) from Sequences module
\*    which accumulates over the sequence from left to right.
SeqReduce(f, acc, seq) == \* f is binary, acc identity
          IF seq = <<>> THEN acc ELSE
          f(\* element \*, acc) \* applied inductively

\* Example: SumSeq(seq) == SeqReduce(\Add, 0, seq)

\* (5) Find the index of an element in a sequence (returns the first index, 1-based)
IndexOf(e, seq) ==
    IF e \in set(seq) THEN
        LEAST i \in DOMAIN seq : seq[i] = e
    ELSE
        0

\* (6) Convert a sequence to the set of its elements
SeqToSet(seq) == set(seq)

\* (7) Get the last element of a sequence (returns the empty set if the sequence is empty)
Last(seq) == IF seq = <<>> THEN {} ELSE seq[Len(seq)]

\* (8) Test if a sequence is empty
IsEmpty(seq) == seq = <<>>

\* (9) Remove all occurrences of an element from a sequence
RemoveAll(e, seq) ==
    Filter(seq, x |-> x # e)

\* (10) Intersection of a set of sets
SetOfSetsIntersection(ss) ==
    IF ss = {} THEN {} ELSE
    \prod s \in ss : s

\* (11) Generate all permutation sequences of a finite set
\* Using the standard recursive definition: permutations of empty set is a set containing the empty sequence
Permutations(S) ==
    IF S = {} THEN {{{}}}
    ELSE
        \{ Append(p, <<x>>) :
              x \in S &
              p \in Permutations(S \ {x}) \}

\* (12) Test helper that returns a boolean and prints diagnostic information on failure
TestHelper(cond, msg) ==
    IF cond THEN TRUE ELSE
        \* In practice, TLC does not support printing from the spec; so we just return FALSE
        FALSE

\* ----------------------------------------------------------------------
\* CONSTANTS (none declared here; they are defined by the calling module)
\* ----------------------------------------------------------------------
\* The specification, INIT, NEXT, INVARIANTS, and PROPERTIES operators are
\* defined as empty, because this module is purely functional.
SPECIFICATION == UNCHANGED <<>>

INIT == UNCHANGED <<>>

NEXT == UNCHANGED <<>>

INVARIANTS == {}

PROPERTIES == {}

====