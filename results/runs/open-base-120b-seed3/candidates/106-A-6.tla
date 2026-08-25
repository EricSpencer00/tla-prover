---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ------------------------------------------------------------------------ *)
(* Utility operators *)

(* 1. Set intersection test – do two sets overlap? *)
SetOverlap?(S, T) == (S \cap T) # {}

(* 2. Maximum element of a non‑empty set (assumes a total order) *)
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x

(* 3. Minimum element of a non‑empty set *)
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y

(* 4. Generalized set reduction (fold over a set) *)
RECURSIVE SetReduce(_,_,_)
SetReduce(S, init, f) ==
  IF S = {} THEN init
  ELSE LET e == CHOOSE x \in S IN
       SetReduce(S \ {e}, f(init, e), f)

(* 5. Sequence reduction (fold over a sequence) *)
RECURSIVE SeqReduce(_,_,_)
SeqReduce(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE SeqReduce(Tail(seq), f(init, Head(seq)), f)

(* 6. Index of an element in a sequence (1‑based, 0 if not present) *)
IndexOf(seq, elem) ==
  IF elem \notin SeqToSet(seq) THEN 0
  ELSE
    LET Find(i) ==
      IF i > Len(seq) THEN 0
      ELSE IF seq[i] = elem THEN i
      ELSE Find(i + 1)
    IN Find(1)

(* 7. Convert a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1 .. Len(seq) }

(* 8. Get the last element of a sequence (NULL if empty) *)
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 9. Test whether a sequence is empty *)
IsEmpty(seq) == Len(seq) = 0

(* 10. Remove all occurrences of an element from a sequence *)
RECURSIVE RemoveAll(_,_)
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

(* 11. Intersection of a set of sets *)
SetIntersection(SS) == { x : \A Y \in SS : x \in Y }

(* 12. Generate all permutations of a finite set *)
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 13. Test helper for assertions that prints diagnostic information on failure *)
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE (Print(msg); FALSE)

(* ------------------------------------------------------------------------ *)
(* Trivial specification placeholders required by the .cfg *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====