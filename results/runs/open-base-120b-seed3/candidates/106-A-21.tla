---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

(* 1. Set overlap test *)
SetOverlap(S, T) == (S \cap T) # {}

(* 2. Maximum element of a set (assumes a total order, e.g., Naturals) *)
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x >= y

(* 2. Minimum element of a set *)
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold) *)
SetReduce(S, init, f) ==
  IF S = {} THEN init
  ELSE
    LET x == CHOOSE e \in S IN
      SetReduce(S \ {x}, f(init, x), f)

(* 4. Sequence reduction (fold) *)
SeqReduce(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE SeqReduce(Tail(seq), f(init, Head(seq)), f)

(* 5. Index of an element in a sequence (1‑based, 0 if absent) *)
IndexOf(seq, elem) ==
  IF Len(seq) = 0 THEN 0
  ELSE IF Head(seq) = elem THEN 1
  ELSE
    LET i == IndexOf(Tail(seq), elem) IN
      IF i = 0 THEN 0 ELSE i + 1

(* 6. Convert a sequence to the set of its elements *)
SeqToSet(seq) ==
  { e : \E i \in 1..Len(seq) : seq[i] = e }

(* 7. Last element of a sequence *)
Last(seq) ==
  IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 8. Test if a sequence is empty *)
IsEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence *)
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

(* 10. Intersection of a set of sets *)
SetIntersection(Sets) ==
  IF Sets = {} THEN {}
  ELSE \INTERSECTION Sets

(* 11. Generate all permutations of a finite set *)
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE
    UNION { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

(* 12. Test helper that prints a message on failure *)
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE Print(msg) /\ FALSE

(* Trivial specification scaffolding required by the task *)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED <<>>
INVARIANTS == {}
PROPERTIES == {}

====