---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*=====================================================================
\* Utility operators
\*=====================================================================

\* 1. Set intersection test (whether two sets overlap)
Overlaps(S, T) == \E x \in S : x \in T

\* 2. Maximum element of a non‑empty finite set of numbers
Max(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S :
        \A y \in S : y <= x

\* 3. Minimum element of a non‑empty finite set of numbers
Min(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S :
        \A y \in S : y >= x

\* 4. Generalized set reduction (fold over a set with an accumulator)
\*    op is a binary operator given as a two‑argument lambda (a,b) |-> expr
SetReduce(S, init, op) ==
  IF S = {} THEN init
  ELSE
    LET x == CHOOSE e \in S : TRUE
    IN SetReduce(S \ {x}, op(init, x), op)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
\*    Uses the built‑in FoldSeq operator from the Sequences module.
SeqReduce(seq, init, op) == FoldSeq(seq, init, op)

\* 6. Finding the index of an element in a sequence (0 if absent)
SeqIndex(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem
  THEN Min({ i \in 1..Len(seq) : seq[i] = elem })
  ELSE 0

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Getting the last element of a sequence (undefined if empty)
Last(seq) == seq[Len(seq)]

\* 9. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) == << seq[i] : i \in 1..Len(seq) /\ seq[i] # elem >>

\* 11. Computing the intersection of a set of sets
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE
    LET first == CHOOSE S \in SS : TRUE
    IN SetReduce(SS \ {first}, first, (A,B) |-> A \cap B)

\* 12. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE
    UNION { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for assertions that prints diagnostic info on failure
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE (Print(msg); FALSE)

\*=====================================================================
\* Dummy specification (required identifiers)
\*=====================================================================

VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====