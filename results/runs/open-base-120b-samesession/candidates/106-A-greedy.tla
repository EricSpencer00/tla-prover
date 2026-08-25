---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES dummy

(*--------------------------------------------------------------------
  Trivial state machine (required identifiers)
--------------------------------------------------------------------*)
Init == dummy = TRUE

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

(*--------------------------------------------------------------------
  Utility operators
--------------------------------------------------------------------*)

(* 1. Set overlap test: true iff two sets have a non‑empty intersection *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum element of a non‑empty set (assumes a total order) *)
SetMax(S) == 
  CHOOSE x \in S : \A y \in S : y <= x

(* 2b. Minimum element of a non‑empty set (assumes a total order) *)
SetMin(S) == 
  CHOOSE x \in S : \A y \in S : y >= x

(* 3. Generalized set reduction (fold) *)
RECURSIVE SetFold(_, _, _)
SetFold(S, init, f) ==
  IF S = {} THEN init
  ELSE 
    LET e == CHOOSE x \in S : TRUE
    IN SetFold(S \ {e}, f(init, e), f)

(* 4. Sequence reduction (fold) *)
RECURSIVE SeqFold(_, _, _)
SeqFold(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE SeqFold(SeqTail(seq), f(init, seq[1]), f)

(* 5. Index of an element in a sequence (returns -1 if not present) *)
SeqIndex(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE -1

(* 6. Convert a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Last element of a non‑empty sequence *)
SeqLast(seq) == seq[Len(seq)]

(* 8. Test if a sequence is empty *)
SeqIsEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence *)
RECURSIVE SeqRemoveAll(_,_)
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem
        THEN SeqRemoveAll(SeqTail(seq), elem)
        ELSE <<seq[1]>> \o SeqRemoveAll(SeqTail(seq), elem)

(* 10. Intersection of a set of sets *)
SetIntersectionAll(SS) ==
  IF SS = {} THEN {}
  ELSE INTERSECTION SS

(* 11. Generate all permutations of a finite set as a set of sequences *)
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

SetPermutations(S) == Permutations(S)

(* 12. Assertion helper that prints a message on failure (TLC) *)
AssertHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE Print(msg) /\ FALSE

====