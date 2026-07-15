---- MODULE Util ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANTS
  \* No constants are required by the .cfg, but we declare the set of
  \* all possible values that our operators may work with.  This allows
  \* the model checker to enumerate a finite domain.
  Values

VARIABLES
  unused   \* No state is needed; a dummy variable satisfies the TLC
            \* requirement that a spec contain at least one variable.

\*=============================================================================
\* Helper definitions (not required by the .cfg but useful internally)
\*=============================================================================
EmptySeq == << >>

\*=============================================================================
\* Operators required by the description
\*=============================================================================

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == 
  \E x \in S : x \in T

\* 2. Maximum element selection from a set
SetMax(S) == 
  IF S = {} THEN CHOOSE x : x \in {}
  ELSE 
    LET m == \CHOOSE y \in S : \A z \in S : y >= z IN m

\* 3. Minimum element selection from a set
SetMin(S) == 
  IF S = {} THEN CHOOSE x : x \in {}
  ELSE 
    LET m == \CHOOSE y \in S : \A z \in S : y <= z IN m

\* 4. Generalized set reduction (fold over a set with an accumulator)
SetFold(Fun, Set, Init) ==
  IF Set = {} THEN Init
  ELSE 
    LET x \in Set IN
      SetFold(Fun, Set \ {x}, Fun(Init, x))

\* 5. Sequence reduction (fold over a sequence with an accumulator)
SeqFold(Fun, Seq, Init) ==
  FoldLeft(Fun, Seq, Init)   \* FoldLeft is provided by the Sequences module

\* 6. Finding the index of an element in a sequence (1‑based)
SeqIndex(Seq, elem) ==
  IF elem \notin Seq THEN 0
  ELSE
    CHOOSE i \in DOMAIN Seq : Seq[i] = elem

\* 7. Converting a sequence to the set of its elements
SeqToSet(Seq) ==
  { Seq[i] : i \in DOMAIN Seq }

\* 8. Getting the last element of a sequence
SeqLast(Seq) ==
  IF Seq = EmptySeq THEN CHOOSE x : FALSE
  ELSE Seq[Len(Seq)]

\* 9. Testing if a sequence is empty
SeqEmpty(Seq) ==
  Len(Seq) = 0

\* 10. Removing all occurrences of an element from a sequence
SeqRemoveAll(Seq, elem) ==
  [ i \in 1..(Len(Seq) - Count(Seq, elem)) |-> 
      IF i < (SeqIndex(Seq, elem)) THEN Seq[i]
      ELSE Seq[i + Count(Seq, elem)] ]

\* 11. Computing the intersection of a set of sets
SetOfSetsIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE
    LET First == CHOOSE s \in SS : TRUE IN
      \A s \in SS : First \subseteq s
      \* The above ensures all sets contain the same elements;
      \* the actual intersection is then:
    { x \in First : \A s \in SS : x \in s }

\* 12. Generating all permutation sequences of a finite set
SetPermutations(S) ==
  IF S = {} THEN { << >> }
  ELSE
    UNION { { << e >> \o p | p \in SetPermutations(S \ {e}) } : e \in S }

\* 13. Test helper that prints diagnostic information on failure
TestHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE
    BEGIN
      Print(msg);
      FALSE
    END

\*=============================================================================
\* Specification required by the .cfg (dummy state machine)
\*=============================================================================

SPECIFICATION == Init /\ [][Next]_<<unused>>

Init ==
  /\ unused \in BOOLEAN
  /\ unused' = unused

Next ==
  /\ unused' = ~unused

\* The .cfg does not require any additional operators, but we expose the
\* library operators with the exact names requested in the description.
\* They are already defined above.

=============================================================================