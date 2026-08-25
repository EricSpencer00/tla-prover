---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Utility operators for set and sequence manipulation                    *)
(***************************************************************************)

\* 1. Set intersection test (whether two sets overlap)
Overlaps(S, T) == /\ S # {} /\ T # {} /\ \E x \in S : x \in T

\* 2. Maximum element of a set (assumes elements are comparable, e.g., numbers)
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x >= y

\*    Minimum element of a set
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, init, op) ==
  IF S = {} THEN init
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN op(x, SetReduce(S \ {x}, init, op))

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqTail(seq) == IF Len(seq) = 0 THEN <<>> ELSE SubSeq(seq, 2, Len(seq))

SeqReduce(seq, init, op) ==
  IF Len(seq) = 0 THEN init
  ELSE op(seq[1], SeqReduce(SeqTail(seq), init, op))

\* 5. Finding the index of an element in a sequence (1..Len, 0 if absent)
IndexOf(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE 0

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
Last(seq) == seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem THEN RemoveAll(SeqTail(seq), elem)
  ELSE << seq[1] >> \o RemoveAll(SeqTail(seq), elem)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE
    LET S0 == CHOOSE s \in SS : TRUE
    IN S0 \cap SetIntersection(SS \ {S0})

\* 11. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE UNION { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for writing assertions (prints diagnostics on failure
\*    in the TLC UI; here defined as a simple Boolean check)
Assert(cond, msg) == cond

(***************************************************************************)
(*  Stubs required by the reference .cfg (no identifiers are actually   *)
(*  needed, but they must exist)                                         *)
(***************************************************************************)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED <<>>
INVARIANTS == {}
PROPERTIES == {}

=============================================================================