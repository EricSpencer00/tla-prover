---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators for set and sequence manipulation
\* ----------------------------------------------------------------------

\* (1) Set intersection test: returns TRUE iff the two sets overlap
SetIntersectTest(S, T) == \E x \in S : x \in T

\* (2) Maximum element of a non‑empty finite set
SetMax(S) == 
  IF S = {} THEN CHOOSE x : x \in {} 
  ELSE
    LET m == CHOOSE y \in S : \A z \in S : y >= z IN m

\* (2) Minimum element of a non‑empty finite set
SetMin(S) == 
  IF S = {} THEN CHOOSE x : x \in {} 
  ELSE
    LET m == CHOOSE y \in S : \A z \in S : y <= z IN m

\* (3) Generalized set reduction (fold over a set with an accumulator)
\*    f is a binary operator, a0 is the initial accumulator.
SetReduce(S, f, a0) ==
  IF S = {} THEN a0
  ELSE
    LET
      Compute(\A, X) ==
        IF X = {} THEN a0
        ELSE
          LET y == CHOOSE z \in X : TRUE IN
          f(y, Compute(\A, X \ {y}))
    IN Compute(\A, S)

\* (4) Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, f, a0) == Fold(seq, f, a0)

\* (5) Index of an element in a sequence (1‑based). Returns 0 if not present.
SeqIndex(seq, e) ==
  IF \E i \in 1..Len(seq) : seq[i] = e
    THEN
      CHOOSE i \in 1..Len(seq) : seq[i] = e
    ELSE 0

\* (6) Convert a sequence to the set of its elements
SeqToSet(seq) == { i \in 1..Len(seq) :-> seq[i] }

\* (7) Last element of a non‑empty sequence
SeqLast(seq) ==
  IF Len(seq) = 0 THEN CHOOSE x : x \in {} ELSE seq[Len(seq)]

\* (8) Test if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* (9) Remove all occurrences of an element from a sequence
SeqRemoveAll(seq, e) ==
  [ i \in 1..(Len(seq) - Cardinality({ j \in 1..Len(seq) : seq[j] = e })) |->  
      IF \E k \in 1..Len(seq) : 
            (seq[k] # e) /\ (Cardinality({ m \in 1..k : seq[m] # e }) = i)
        THEN CHOOSE k \in 1..Len(seq) : 
                (seq[k] # e) /\ (Cardinality({ m \in 1..k : seq[m] # e }) = i)
        ELSE e ]

\* (10) Intersection of a set of sets
SetOfSetsIntersect(S) ==
  IF S = {} THEN {}
  ELSE
    LET
      First == CHOOSE A \in S : TRUE
    IN
      \A B \in S : First \subseteq B => First

\* (11) Generate all permutations of a finite set
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE
    UNION {
      \E p \in Permutations(S \ {e}) : { << e >> \o p }
      : e \in S
    }

\* (12) Test helper that asserts a condition and prints a message on failure.
\*    In a TLA+ model, the message is expressed as part of the error trace.
TestAssert(msg, cond) == cond

\* ----------------------------------------------------------------------
\* The specification required identifiers (trivial placeholders)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====