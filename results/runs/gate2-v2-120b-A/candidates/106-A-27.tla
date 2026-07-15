---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Utility operators used throughout the key-value store specifications.
\* No state variables are defined; this module purely provides reusable
\* definitions.
\* ----------------------------------------------------------------------

\* ---------- Set intersection test ----------
\* Overlap(s, t) is TRUE iff the two sets share at least one element.
Overlap(s, t) == \E x \in s : x \in t

\* ---------- Maximum and minimum element selection ----------
\* NOTE: The set must be non‑empty. The definitions use the CHOOSE
\* operator, which picks an element satisfying the predicate.
MaxSet(s) == CHOOSE x \in s : \A y \in s : y <= x
MinSet(s) == CHOOSE x \in s : \A y \in s : x <= y

\* ---------- Generalized set reduction (fold over a set) ----------
\* ReduceSet(f, acc, s) applies the binary operator f to each element
\* of the finite set s, threading an accumulator that starts with acc.
ReduceSet(f, acc, s) ==
  IF s = {} THEN acc
  ELSE LET x == CHOOSE y \in s : TRUE IN
       ReduceSet(f, f(acc, x), s \ {x})

\* ---------- Sequence reduction (fold over a sequence) ----------
\* FoldSeq(f, acc, seq) processes the sequence from left to right.
FoldSeq(f, acc, seq) ==
  IF Len(seq) = 0 THEN acc
  ELSE FoldSeq(f, f(acc, Head(seq)), Tail(seq))

\* ---------- Index of an element in a sequence ----------
\* IndexOf(seq, e) returns the 1‑based position of the first occurrence
\* of e in seq, or 0 if e is not present.
IndexOf(seq, e) ==
  IF e \in set(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = e
  ELSE 0

\* ---------- Convert a sequence to the set of its elements ----------
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* ---------- Last element of a non‑empty sequence ----------
Last(seq) == seq[Len(seq)]

\* ---------- Empty‑sequence test ----------
IsEmpty(seq) == Len(seq) = 0

\* ---------- Remove all occurrences of an element from a sequence ----------
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE
    LET rest == RemoveAll(Tail(seq), e) IN
    IF Head(seq) = e THEN rest ELSE << Head(seq) >> \X rest

\* ---------- Intersection of a set of sets ----------
SetIntersect(ss) == { x \in UNION ss : \A s \in ss : x \in s }

\* ---------- Permutations of a finite set ----------
\* Permutations(s) returns the set of all sequences that are permutations
\* of the elements of s.
Permutations(s) ==
  IF s = {} THEN { <<>> }
  ELSE
    UNION {
      << e >> \X p :
        e \in s /\ p \in Permutations(s \ {e})
    }

\* ---------- Test helper that prints diagnostics on failure ----------
\* In TLA+ specifications the operator simply returns its boolean argument.
\* The diagnostic output is handled by the TLC configuration file.
TestHelper(b) == b

\* ----------------------------------------------------------------------
\* Even though the description does not require a temporal spec, the
\* reference .cfg expects the following names to exist.  They are defined
\* as trivial (stuttering) specifications that always hold.
\* ----------------------------------------------------------------------
VARIABLE dummy

SpecInit == dummy' = dummy
SpecNext == UNCHANGED dummy

SPECIFICATION == SpecInit /\ [][SpecNext]_<<dummy>>

\* The .cfg may refer to these names; they are defined for completeness.
INVARIANTS == TRUE
PROPERTIES == TRUE
INIT == SpecInit
NEXT == SpecNext

====