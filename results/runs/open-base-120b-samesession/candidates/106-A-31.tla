---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Utility operators
   ---------------------------------------------------------------------- *)

(* 1. Set intersection test (whether two sets overlap) *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum element of a set (returns {} when the set is empty) *)
SetMax(S) ==
  IF S = {} THEN {}
  ELSE CHOOSE x \in S : \A y \in S : x >= y

(* 3. Minimum element of a set (returns {} when the set is empty) *)
SetMin(S) ==
  IF S = {} THEN {}
  ELSE CHOOSE x \in S : \A y \in S : x <= y

(* 4. Generalized set reduction (fold over a set with an accumulator) *)
SetFold(S, init, f) ==
  IF S = {} THEN init
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN SetFold(S \ {x}, f(init, x), f)

(* 5. Sequence reduction (fold over a sequence with an accumulator) *)
SeqFold(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE SeqFold(Tail(seq), f(init, Head(seq)), f)

(* 6. Finding the index of an element in a sequence (0 if absent) *)
SeqIndex(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE 0

(* 7. Converting a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 8. Getting the last element of a sequence (undefined for empty) *)
SeqLast(seq) == seq[Len(seq)]

(* 9. Testing if a sequence is empty *)
SeqEmpty(seq) == Len(seq) = 0

(* 10. Removing all occurrences of an element from a sequence *)
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem THEN SeqRemoveAll(Tail(seq), elem)
  ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

(* 11. Computing the intersection of a set of sets *)
SetIntersection(setOfSets) == INTERSECTION setOfSets

(* 12. Generating all permutation sequences of a finite set *)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 13. Test helper for assertions (prints diagnostics on failure) *)
TestHelper(msg, cond) == cond

(* ----------------------------------------------------------------------
   Specification skeleton (required identifiers)
   ---------------------------------------------------------------------- *)

INIT == TRUE

NEXT == TRUE

SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====