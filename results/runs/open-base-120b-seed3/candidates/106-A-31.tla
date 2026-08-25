---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Utility operators
   ---------------------------------------------------------------------- *)

(* 1. Set overlap test *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum and minimum element of a set (assumes numeric elements) *)
SetMax(S) ==
  IF S = {} THEN NULL ELSE Max(S)

SetMin(S) ==
  IF S = {} THEN NULL ELSE Min(S)

(* 3. Generalized set reduction (fold) *)
SetFold(S, init, op) ==
  IF S = {} THEN init
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN SetFold(S \ {x}, op(init, x), op)

(* 4. Sequence reduction (fold) *)
SeqFold(seq, init, op) ==
  IF Len(seq) = 0 THEN init
  ELSE
    LET rest == SubSeq(seq, 1, Len(seq) - 1)
        last == seq[Len(seq)]
    IN op(SeqFold(rest, init, op), last)

(* 5. Index of an element in a sequence (first occurrence, -1 if absent) *)
SeqIndex(seq, elem) ==
  IF elem \in seq THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE -1

(* 6. Convert a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Last element of a sequence (NULL if empty) *)
SeqLast(seq) ==
  IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 8. Test if a sequence is empty *)
SeqIsEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence *)
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN << >>
  ELSE IF seq[1] = elem THEN
         SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)
       ELSE
         << seq[1] >> \o SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)

(* 10. Intersection of a set of sets *)
SetIntersectionOfSets(SS) ==
  IF SS = {} THEN {}
  ELSE { x \in UNION SS : \A S \in SS : x \in S }

(* 11. All permutations of a finite set *)
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE UNION {
        << x >> \o p :
          x \in S,
          p \in Permutations(S \ {x})
      }

(* 12. Test helper that prints a diagnostic message on failure *)
TestHelper(expr, msg) ==
  IF expr THEN TRUE
  ELSE (Print(msg); FALSE)

(* ----------------------------------------------------------------------
   Minimal specification skeleton (required identifiers)
   ---------------------------------------------------------------------- *)

VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====