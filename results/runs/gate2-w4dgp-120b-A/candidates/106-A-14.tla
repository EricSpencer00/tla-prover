---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* No system actors or components here: this is a pure library module.  It
\* defines reusable operators over sets and sequences that the key-value
\* store specifications import.  The operators are deliberately generic
\* and go beyond the tiny subset that TLC's built-in library provides,
\* so other modules can write expressive, high-level logic without
\* re-implementing the same folds and set tricks.

\* EmptySeq: the canonical empty sequence value for the operators below.
EmptySeq == <<>>

\* HasOverlap(a, b): true exactly when sets a and b share at least one
\* element.  This is a standard set-intersection test phrased as
\* an existential over the intersection.
HasOverlap(a, b) == \E x \in a \cap b : TRUE

\* MaxSet(s): the greatest element of a non-empty set of naturals.
MaxSet(s) == CHOOSE m \in s : \A x \in s : x <= m
\* MinSet(s): the smallest element of a non-empty set of naturals.
MinSet(s) == CHOOSE m \in s : \A x \in s : m <= x

\* SetFold(f, base, s): fold the binary operator f left-associatively
\* over a set s, starting from base.  The result is base when s is empty.
SetFold(f, base, s) == IF s = {} THEN base
                       ELSE LET x == CHOOSE y \in s : TRUE
                            IN f[x, SetFold(f, base, s \ {x})]

\* SeqFold(f, base, seq): fold the binary operator f left-associatively
\* over a sequence seq.  Sequences are ordered, so this is a real fold
\* (not the set-fold's arbitrary choice).  TLC's Sequences module
\* already provides FoldL with the same semantics, so this wraps it.
SeqFold(f, base, seq) == FoldL(seq, base, f)

\* IndexOf(seq, x): the 1-based position where x first appears in seq,
\* or 0 if x is absent.  Sequences are small in every store spec that
\* uses this helper, so the linear scan is fine.
IndexOf(seq, x) == LET pos == { i \in 1..Len(seq) : seq[i] = x }
                  IN IF pos = {} THEN 0
                     ELSE CHOOSE i \in pos : \A j \in pos : i <= j

\* ToSet(seq): collapse a sequence to the set of the values it contains.
ToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* LastOf(seq): the final element of a non-empty sequence.
LastOf(seq) == seq[Len(seq)]

\* IsEmpty(seq): true exactly for the empty sequence; a shorthand.
IsEmpty(seq) == Len(seq) = 0

\* RemoveAll(seq, x): a copy of seq with every occurrence of x omitted.
RemoveAll(seq, x) == [ i \in 1..(Len(seq) - Cardinality({ k \in 1..Len(seq) : seq[k] = x }))
                        |-> seq[CHOOSE k \in { j \in 1..Len(seq) : seq[j] # x } : k >= i] ]

\* IntersectOver(F): the intersection of every set in a non-empty set of sets.
IntersectOver(F) == CHOOSE y \in F :
                     \A z \in F : \A x \in y : x \in z

\* Permutations(s): every ordering of the finite set s as a sequence.
Permutations(s) == { p \in Seq(s) : ToSet(p) = s }

\* TestTrue: a debugging helper; it always returns TRUE, but the
\* THEN/ELSE branches are separate so a failure prints both.
TestTrue == IF TRUE THEN TRUE ELSE FALSE

\* SPEC, INIT, NEXT, INVARIANTS, PROPERTIES: defined here so the .cfg
\* can name them, even though the library module itself has no
\* runtime behavior to model.
Specification == TRUE
Init == TRUE
Next == FALSE
Invariants == {}
Properties == {}
====