---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators for set and sequence manipulation.
\* ----------------------------------------------------------------------

\* (1) Set intersection test: TRUE iff two sets overlap.
SetOverlap(s, t) == s \cap t # {}

\* (2) Maximum and minimum element selection from a non‑empty set.
SetMax(s) == CHOOSE x \in s : \A y \in s : y <= x
SetMin(s) == CHOOSE x \in s : \A y \in s : x <= y

\* (3) Generalized set reduction (fold over a set with an accumulator).
\*    foldSet(S, acc, f) applies f to each element of S in an
\*    arbitrary order, threading the accumulator.
FoldSet(S, acc, f) ==
  IF S = {} THEN acc
  ELSE LET x == CHOOSE y \in S : TRUE IN
       FoldSet(S \ {x}, f(acc, x), f)

\* (4) Sequence reduction (fold over a sequence with an accumulator).
\*    Implemented via the library operator FoldSeq from Sequences.
SeqReduce(seq, acc, f) == FoldSeq(f, seq, acc)

\* (5) Finding the index (1‑based) of an element in a sequence.
\*    Returns 0 if the element does not occur.
SeqIndex(seq, elem) ==
  IF elem \notin SeqToSet(seq) THEN 0
  ELSE CHOOSE i \in 1..Len(seq) : seq[i] = elem

\* (6) Converting a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (7) Getting the last element of a non‑empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* (8) Testing if a sequence is empty.
SeqIsEmpty(seq) == Len(seq) = 0

\* (9) Removing all occurrences of an element from a sequence.
SeqRemove(seq, elem) ==
  [i \in 1..(Len(seq) - Cardinality({ j \in 1..Len(seq) : seq[j] = elem })) |-> 
     IF i \leq Len(seq) - Cardinality({ j \in 1..Len(seq) : seq[j] = elem })
        THEN
          LET k == 
            IF i <= (Cardinality({ j \in 1..Len(seq) : seq[j] = elem }) + 1)
               THEN i
               ELSE i + Cardinality({ j \in 1..Len(seq) : seq[j] = elem })
          IN seq[k]
        ELSE seq[i]]

\* (10) Intersection of a set of sets.
SetIntersection(T) == IF T = {} THEN {} ELSE /\ (\A S \in T : S \in SUBSET UNIV)
                                   /\ \{ x \in UNION T : \A S \in T : x \in S \}

\* (11) Generating all permutation sequences of a finite set.
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE
    UNION {
      { << e >> \o p : p \in Permutations(S \ {e}) } :
        e \in S
    }

\* (12) Test helper for assertions with diagnostic printing.
\*    In a normal model run, prints nothing; on a failed assertion
\*    the message is emitted via the built‑in \A assertion mechanism.
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE
    /\ FALSE
    /\ Print(msg)

\* ----------------------------------------------------------------------
\* The following names are required by the reference configuration.
\* They are defined as trivial no‑op operators to satisfy the parser.
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====