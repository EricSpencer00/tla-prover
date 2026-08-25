---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

RECURSIVE SetFold(_,_ ,_), SeqFold(_,_ ,_), RemoveAll(_,_), SetIntersection(_), SetPermutations(_)

(* Sentinel value used for empty‑set or empty‑sequence results *)
Null == "NULL"

(* 1. Set intersection test *)
Overlap(S, T) == (S \cap T) # {}

(* 2. Maximum element of a set (Null for empty set) *)
SetMax(S) == IF S = {} THEN Null ELSE CHOOSE x \in S: \A y \in S: x >= y

(* 2. Minimum element of a set (Null for empty set) *)
SetMin(S) == IF S = {} THEN Null ELSE CHOOSE x \in S: \A y \in S: x <= y

(* 3. Generalized set reduction (fold) *)
SetFold(S, acc, f(_,_)) ==
  IF S = {} THEN acc
  ELSE LET x == CHOOSE y \in S: TRUE
       IN SetFold(S \ {x}, f(acc, x), f)

(* 4. Sequence reduction (fold) *)
SeqFold(seq, acc, f(_,_)) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqFold(SubSeq(seq, 2, Len(seq)), f(acc, Head(seq)), f)

(* 5. Index of an element in a sequence (0 if not present) *)
IndexOf(seq, elt) ==
  IF \E i \in 1..Len(seq) : seq[i] = elt
  THEN CHOOSE i \in 1..Len(seq) : seq[i] = elt
  ELSE 0

(* 6. Convert a sequence to a set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Last element of a sequence (Null for empty) *)
Last(seq) == IF Len(seq) = 0 THEN Null ELSE seq[Len(seq)]

(* 8. Test if a sequence is empty *)
SeqIsEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence *)
RemoveAll(seq, elt) ==
  IF Len(seq) = 0
  THEN <<>>
  ELSE IF Head(seq) = elt
       THEN RemoveAll(SubSeq(seq, 2, Len(seq)), elt)
       ELSE <<Head(seq)>> \o RemoveAll(SubSeq(seq, 2, Len(seq)), elt)

(* 10. Intersection of a set of sets *)
SetIntersection(Sets) ==
  IF Sets = {} THEN {}
  ELSE LET s == CHOOSE A \in Sets: TRUE
       IN s \cap SetIntersection(Sets \ {s})

(* 11. All permutations of a finite set *)
SetPermutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in SetPermutations(S \ {e}) }

(* 12. Assertion helper that prints diagnostic info on failure *)
UtilAssert(cond, msg) ==
  IF cond THEN TRUE ELSE Print(msg, TRUE) /\ FALSE

(* Trivial placeholders required by the configuration *)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====