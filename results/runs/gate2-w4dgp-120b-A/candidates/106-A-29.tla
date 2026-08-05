---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Utility library module shared by the key-value store specifications. It
\* provides a suite of reusable operators for set and sequence manipulation:
\* intersection, reduction (fold) over sets and sequences, sequence indexing,
\* conversion of a sequence to a set, last-element extraction, emptiness test,
\* removal of all occurrences of an element from a sequence, set-of-sets
\* intersection, permutation generation, and a test-helper with diagnostic
\* output. The module has no actors or system components; its purpose is to
\* encapsulate common functional utilities so that the main specifications
\* remain concise and focused on their specific domain logic.

CONSTANTS

\* No actors or components are defined here, so the configuration section that
\* drives the model checker must inherit its CONSTANTS from the importing
\* module(s) that actually use this library. This is intentional: the library
\* simply makes the operators available; the shape of the model it participates
\* in is defined elsewhere.

INTERSECT(s, t) == s \cap t # {}

\* Returns the greatest element in a set of naturals, or 0 for the empty set.
MaxElem(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z IN x

\* Returns the smallest element in a set of naturals, or 0 for the empty set.
MinElem(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : \A z \in S : y <= z IN x

\* Fold over a set, applying an associative binary operator to accumulate a
\* result. The base case is the neutral element for the operator.
SetFold(f, S, e) == IF S = {} THEN e ELSE LET x == CHOOSE y \in S : TRUE IN f[x, SetFold(f, S \ {x}, e)]

SeqFold(f, seq, e) == IF seq = <<>> THEN e ELSE f[Head(seq), SeqFold(f, Tail(seq), e)]

\* Returns the 1-indexed position of element x in sequence seq, or 0 if x is
\* absent. Works for sequences that may contain repeated elements.
IndexOf(seq, x) == IF seq = <<>> THEN 0
                   ELSE IF Head(seq) = x THEN 1
                   ELSE LET i == IndexOf(Tail(seq), x) IN IF i = 0 THEN 0 ELSE i + 1

SeqToSet(seq) == SetFold(LAMBDA p, q : p \cup {q}, seq, {})

\* Returns the last element of a non-empty sequence.
Last(seq) == IF Tail(seq) = <<>> THEN Head(seq) ELSE Last(Tail(seq))

EmptySeq(seq) == seq = <<>>

\* Removes all occurrences of element x from a sequence.
RemoveAll(seq, x) == IF seq = <<>> THEN <<>>
                     ELSE IF Head(seq) = x THEN RemoveAll(Tail(seq), x)
                     ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), x)

\* Computes the intersection of a collection of sets.
IntersectAll(S) == IF S = {} THEN {}
                   ELSE LET x == CHOOSE y \in S : TRUE IN x \cap IntersectAll(S \ {x})

\* Generates every permutation of a finite set as a sequence. For a set of
\* size n it produces n! distinct sequences.
Permutations(S) == IF S = {} THEN {<<>>}
                    ELSE UNION { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* Test helper that asserts a condition and, on failure, prints the name of the
\* failed check and the current values of the indicated symbols before aborting.
Check(cond, name, symbols) == IF cond THEN TRUE
                             ELSE (PrintT("FAILED:", name), PrintT(symbols), FALSE)

====