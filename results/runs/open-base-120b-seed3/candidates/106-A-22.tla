---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* 1. Set intersection test *)
Overlaps(S, T) == (S \cap T) # {}

(* 2. Maximum and minimum element selection from a set (assumes a total order) *)
Max(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S: \A y \in S: x >= y

Min(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S: \A y \in S: x <= y

(* 3. Helpers for sequence manipulation *)
Head(s) == s[1]
Tail(s) == [i \in 1..Len(s)-1 |-> s[i+1]]

(* 4. Generalized set reduction (fold over a set) *)
SetFold(S, op, a0) ==
  IF S = {} THEN a0
  ELSE
    LET x == CHOOSE y \in S: TRUE
    IN SetFold(S \ {x}, op, op(a0, x))

(* 5. Sequence reduction (fold over a sequence) *)
SeqFold(s, op, a0) ==
  IF Len(s) = 0 THEN a0
  ELSE SeqFold(Tail(s), op, op(a0, Head(s)))

(* 6. Index of an element in a sequence; 0 means not found *)
IndexOf(s, e) ==
  IF Len(s) = 0 THEN 0
  ELSE IF Head(s) = e THEN 1
  ELSE
    LET i == IndexOf(Tail(s), e)
    IN IF i = 0 THEN 0 ELSE i + 1

(* 7. Convert a sequence to a set of its elements *)
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

(* 8. Last element of a sequence *)
Last(s) ==
  IF Len(s) = 0 THEN NULL
  ELSE s[Len(s)]

(* 9. Test whether a sequence is empty *)
IsEmpty(s) == Len(s) = 0

(* 10. Remove all occurrences of an element from a sequence *)
RemoveAll(s, e) ==
  IF Len(s) = 0 THEN << >>
  ELSE IF Head(s) = e THEN RemoveAll(Tail(s), e)
  ELSE << Head(s) >> \o RemoveAll(Tail(s), e)

(* 11. Intersection of a set of sets *)
SetInter(S) ==
  IF S = {} THEN {}
  ELSE { x : \A Y \in S : x \in Y }

(* 12. Generate all permutations of a finite set *)
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE UNION { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 13. Assertion helper that prints a diagnostic message on failure *)
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE Print(msg) /\ FALSE

====