---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  \* No constants are required by the .cfg, but we declare a placeholder
  \* to avoid an “undeclared constant” warning if a model adds one.
  dummy

\*---------------------------------------------------------------------- 
\* 1. Set intersection test (whether two sets overlap)
\*---------------------------------------------------------------------- 
SetOverlap(s, t) == \E x \in s : x \in t

\*---------------------------------------------------------------------- 
\* 2. Maximum and minimum element selection from a set
\*---------------------------------------------------------------------- 
SetMax(s) == 
  CHOOSE m \in s : \A n \in s : n <= m

SetMin(s) == 
  CHOOSE m \in s : \A n \in s : m <= n

\*---------------------------------------------------------------------- 
\* 3. Generalized set reduction (fold over a set with an accumulator)
\*    The operator `op` must be a binary operator where the first argument
\*    is the accumulator and the second argument is an element of the set.
\*---------------------------------------------------------------------- 
SetReduce(op, init, s) ==
  IF s = {} THEN init
  ELSE LET x == CHOOSE y \in s : TRUE IN
       SetReduce(op, op(init, x), s \ {x})

\*---------------------------------------------------------------------- 
\* 4. Sequence reduction (fold over a sequence with an accumulator)
\*    We implement this using the built‑in `FoldSeq` operator.
\*---------------------------------------------------------------------- 
SeqReduce(op, init, seq) == FoldSeq(op, init, seq)

\*---------------------------------------------------------------------- 
\* 5. Finding the index of an element in a sequence
\*---------------------------------------------------------------------- 
SeqIndex(seq, elem) ==
  IF elem \notin SeqToSet(seq) THEN -1
  ELSE CHOOSE i \in 1..Len(seq) : seq[i] = elem

\*---------------------------------------------------------------------- 
\* 6. Converting a sequence to the set of its elements
\*---------------------------------------------------------------------- 
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\*---------------------------------------------------------------------- 
\* 7. Getting the last element of a sequence
\*---------------------------------------------------------------------- 
SeqLast(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\*---------------------------------------------------------------------- 
\* 8. Testing if a sequence is empty
\*---------------------------------------------------------------------- 
SeqIsEmpty(seq) == Len(seq) = 0

\*---------------------------------------------------------------------- 
\* 9. Removing all occurrences of an element from a sequence
\*---------------------------------------------------------------------- 
SeqRemoveAll(seq, elem) ==
  [ i \in 1..(Len(seq) - Cardinality({ j \in 1..Len(seq) : seq[j] = elem })) |-> 
      IF i <= (SeqPos(seq, elem) - 1) THEN seq[i]
      ELSE seq[i + Cardinality({ j \in 1..Len(seq) : seq[j] = elem })] ]

\* Helper to compute the position of the first occurrence of elem, or Len(seq)+1 if absent
SeqPos(seq, elem) ==
  IF elem \notin SeqToSet(seq) THEN Len(seq) + 1
  ELSE CHOOSE i \in 1..Len(seq) : seq[i] = elem

\*---------------------------------------------------------------------- 
\* 10. Computing the intersection of a set of sets
\*---------------------------------------------------------------------- 
SetIntersection(sets) ==
  IF sets = {} THEN {}
  ELSE { x \in CHOOSE s \in sets : TRUE : \A t \in sets : x \in t }

\*---------------------------------------------------------------------- 
\* 11. Generating all permutation sequences of a finite set
\*---------------------------------------------------------------------- 
Permutations(s) ==
  IF s = {} THEN <<>>
  ELSE { << e >> \o p : e \in s, p \in Permutations(s \ {e}) }

\*---------------------------------------------------------------------- 
\* 12. Test helper for writing assertions that print diagnostic information
\*---------------------------------------------------------------------- 
TestAssert(cond, msg) == 
  IF cond THEN TRUE ELSE 
    BEGIN 
      Print(msg);
      FALSE
    END

\*---------------------------------------------------------------------- 
\* Boilerplate for the module (not used directly by the library)
\*---------------------------------------------------------------------- 
VARIABLE dummyVar

Init == dummyVar = 0

Next == UNCHANGED dummyVar

Spec == Init /\ [][Next]_<<dummyVar>>

=============================