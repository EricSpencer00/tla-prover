---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*-------------------------------------------------
\* Utility operators
\*-------------------------------------------------

\* (1) Set intersection test – true iff two sets overlap
SetOverlap(S, T) == S ∩ T # {}

\* (2) Maximum element of a non‑empty set
SetMax(S) == 
  IF S = {} THEN 
    CHOOSE x : FALSE \* undefined for empty set
  ELSE 
    CHOOSE m \in S : \A y \in S : y <= m

\* (2) Minimum element of a non‑empty set
SetMin(S) == 
  IF S = {} THEN 
    CHOOSE x : FALSE \* undefined for empty set
  ELSE 
    CHOOSE m \in S : \A y \in S : m <= y

\* (3) Generalized set reduction (fold over a set with an accumulator)
\* f is a binary operator: f(acc, elem)
SetReduce(S, acc, f) ==
  IF S = {} THEN
    acc
  ELSE
    LET x == CHOOSE y \in S IN
      SetReduce(S \ {x}, f(acc, x), f)

\* (4) Sequence reduction (fold over a sequence with an accumulator)
\* f is a binary operator: f(acc, elem)
SeqReduce(seq, acc, f) ==
  IF Len(seq) = 0 THEN
    acc
  ELSE
    SeqReduce(Tail(seq), f(acc, Head(seq)), f)

\* (5) Index of first occurrence of elem in a sequence (1‑based);
\* returns 0 if elem is not present
SeqIndex(seq, elem) ==
  IF elem \in seq THEN
    Min({ i \in 1..Len(seq) : seq[i] = elem })
  ELSE
    0

\* (6) Convert a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (7) Last element of a sequence; returns NULL for empty sequence
SeqLast(seq) ==
  IF Len(seq) = 0 THEN
    NULL
  ELSE
    seq[Len(seq)]

\* (8) Test whether a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* (9) Remove all occurrences of elem from a sequence
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF Head(seq) = elem THEN
    SeqRemoveAll(Tail(seq), elem)
  ELSE
    <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* (10) Intersection of a set of sets
SetIntersectionOfSets(S) == \Inter S

\* (11) Generate all permutations of a finite set S
\* Result is a set of sequences
SetPermutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION { { <<x>> \o p : p \in SetPermutations(S \ {x}) } : x \in S }

\* (12) Test helper for assertions – evaluates expr and returns TRUE;
\* on failure it evaluates to FALSE (TLC can be instructed to print diagnostics)
TestHelper(expr) ==
  IF expr THEN TRUE ELSE FALSE

\*-------------------------------------------------
\* Trivial specification scaffolding required by the .cfg
\*-------------------------------------------------

VARIABLES dummy

Init == dummy = FALSE

Next == dummy' = dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

====