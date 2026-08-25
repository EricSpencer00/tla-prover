---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

(* -------------------------------------------------
   Utility operators
   ------------------------------------------------- *)

(* 1. Set intersection test (whether two sets overlap) *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum element selection from a set *)
SetMax(S) == IF S = {} THEN NULL
            ELSE CHOOSE x \in S : \A y \in S : y <= x

(* 2. Minimum element selection from a set *)
SetMin(S) == IF S = {} THEN NULL
            ELSE CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold over a set) *)
RECURSIVE SetFold(_, _, _)
SetFold(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET e == CHOOSE x \in S : TRUE IN
    SetFold(S \ {e}, f(acc, e), f)

(* 4. Sequence reduction (fold over a sequence) *)
RECURSIVE SeqFold(_, _, _)
SeqFold(seq, acc, f) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqFold(SeqTail(seq), f(acc, SeqHead(seq)), f)

(* 5. Finding the index of an element in a sequence (1‑based, 0 if not found) *)
RECURSIVE SeqIdx(_,_)
SeqIdx(seq, elem) ==
  IF Len(seq) = 0 THEN 0
  ELSE IF SeqHead(seq) = elem THEN 1
  ELSE
    LET idx == SeqIdx(SeqTail(seq), elem) IN
      IF idx = 0 THEN 0 ELSE 1 + idx

(* 6. Converting a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Getting the last element of a sequence *)
SeqLast(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 8. Testing if a sequence is empty *)
SeqIsEmpty(seq) == Len(seq) = 0

(* 9. Removing all occurrences of an element from a sequence *)
RECURSIVE SeqRemoveAll(_, _)
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF SeqHead(seq) = elem THEN SeqRemoveAll(SeqTail(seq), elem)
  ELSE <<SeqHead(seq)>> \o SeqRemoveAll(SeqTail(seq), elem)

(* 10. Computing the intersection of a set of sets *)
SetIntersection(SS) == { x \in UNION SS : \A s \in SS : x \in s }

(* 11. Generating all permutation sequences of a finite set *)
RECURSIVE SetPermutations(_)
SetPermutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE { <<e>> \o p : e \in S, p \in SetPermutations(S \ {e}) }

(* 12. Test helper for writing assertions that print diagnostic information on failure *)
TestHelper(cond, msg) == IF cond THEN TRUE ELSE (Print(msg) /\ FALSE)

(* -------------------------------------------------
   Specification skeleton (no state)
   ------------------------------------------------- *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====