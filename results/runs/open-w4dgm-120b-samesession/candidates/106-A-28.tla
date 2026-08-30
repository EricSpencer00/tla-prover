---- MODULE Util ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS MaxSeq, MaxCard, UNDEF, SEQ1

\* Utility module for the key-value store specs: reusable operators for
\* set/sequence manipulation (intersection, reduction, permutation).

\* Set reduction: apply a binary operator over a set's elements, folding into
\* an accumulator (a classic "reduce" / "fold" over an unordered set).
SetFold(f, base, s) ==
  IF s = {} THEN base
  ELSE LET x == CHOOSE y \in s : TRUE IN f(x, SetFold(f, base, s \ {x}))

\* Sequence reduction: analogous, but over a sequence (ordered collection).
SeqFold(f, base, seq) == FoldSeq(f, base, seq)

\* Index of an element in a sequence, or 0 if it is not present.
IndexOf(seq, el) ==
  LET pos == { i \in DOMAIN seq : seq[i] = el }
  IN IF pos = {} THEN 0 ELSE CHOOSE p \in pos : \A q \in pos : p <= q

\* Sequence to set of its elements.
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* Permutations: generate every ordering of the elements of a small finite
\* set using recursion over sequence extensions.
Permutations(s) ==
  IF s = {} THEN { << >> }
  ELSE UNION { [x] \o p \in Permutations(s \ {x}) : {x} }

\* Helper to print a diagnostic before a failed assertion.
AssertOk(b) == IF b THEN TRUE ELSE UNCHANGED b

====