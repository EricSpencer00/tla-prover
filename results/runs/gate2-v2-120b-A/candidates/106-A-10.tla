---- MODULE Util ----
EXTENDS Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Utility operators for set and sequence manipulation.
--------------------------------------------------------------------*)

(* 1. Set intersection test: whether two sets overlap. *)
SetOverlap(S, T) == S \cap T # {}

(* 2. Maximum and minimum element selection from a set. *)
SetMax(S) ==
  IF S = {} THEN {} ELSE
    CHOOSE x \in S : \A y \in S : y \in S => y <= x

SetMin(S) ==
  IF S = {} THEN {} ELSE
    CHOOSE x \in S : \A y \in S : y \in S => x <= y

(* 3. Generalized set reduction (fold over a set with an accumulator). *)
SetFold(F, Init, S) ==
  IF S = {} THEN Init
  ELSE
    LET f == [s \in S |-> IF s \in DOMAIN @@ THEN
                          F( @@[s], Init)
                        ELSE Init] IN
      [@@ \in S |-> IF @@ = CHOOSE x \in S : TRUE THEN Init ELSE Init]

(* 4. Sequence reduction (fold over a sequence with an accumulator). *)
SeqFold(F, Init, seq) == FoldSeq(F, Init, seq)

(* 5. Finding the index of an element in a sequence (1-based indexing). *)
SeqIndex(seq, elem) ==
  IF elem \in set(seq) THEN
    CHOOSE i \in 1 .. Len(seq) : seq[i] = elem
  ELSE -1

(* 6. Converting a sequence to the set of its elements. *)
SeqToSet(seq) == set(seq)

(* 7. Getting the last element of a sequence. *)
SeqLast(seq) == seq[Len(seq)]

(* 8. Testing if a sequence is empty. *)
SeqIsEmpty(seq) == Len(seq) = 0

(* 9. Removing all occurrences of an element from a sequence. *)
SeqRemoveAll(seq, elem) ==
  [i \in 1 .. Len(seq) - Cardinality({j \in 1 .. Len(seq) : seq[j] = elem}) |
     IF seq[i] # elem THEN seq[i] ELSE seq[i+1]]

(* 10. Computing the intersection of a set of sets. *)
SetIntersectionOfSets(T) ==
  IF T = {} THEN {} ELSE
    \Inter @@ \in T : @@

(* 11. Generating all permutation sequences of a finite set. *)
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE
    UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 12. Test helper for writing assertions that print diagnostic info on failure. *)
TestHelper(condition, message) ==
  IF condition THEN TRUE ELSE
    /\ condition = FALSE
    /\ Print(message)
    /\ FALSE

=============================================================================