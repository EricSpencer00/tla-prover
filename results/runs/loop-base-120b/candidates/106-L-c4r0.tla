---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* 1. Set intersection test: whether two sets overlap *)
SetOverlap(S, T) == \E x \in S: x \in T

(* 2. Maximum and minimum element selection from a set *)
SetMax(S) == IF S = {} THEN NULL ELSE Max(S)
SetMin(S) == IF S = {} THEN NULL ELSE Min(S)

(* 3. Generalized set reduction (fold) *)
SetReduce(S, init, op) == IF S = {} THEN init ELSE FoldSet(S, init, op)

(* 4. Sequence reduction (fold) *)
SeqReduce(seq, init, op) == FoldSeq(seq, init, op)

(* 5. Index of an element in a sequence (0 if not present) *)
IndexOf(seq, elem) ==
  IF \E i \in 1..Len(seq): seq[i] = elem
  THEN CHOOSE i \in 1..Len(seq): seq[i] = elem
  ELSE 0

(* 6. Convert a sequence to a set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Last element of a sequence *)
SeqLast(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 8. Test if a sequence is empty *)
SeqIsEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence *)
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem
       THEN SeqRemoveAll(Tail(seq), elem)
       ELSE <<seq[1]>> \o SeqRemoveAll(Tail(seq), elem)

(* 10. Intersection of a set of sets *)
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE { x \in UNION SS : \A S \in SS: x \in S }

(* 11. All permutations of a finite set *)
Permutations(S) ==
  IF S = {} THEN {<<>>}
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 12. Test helper that prints diagnostic info on failure *)
TestHelper(cond, msg) == cond \/ (Print(msg) /\ FALSE)

(* Trivial specification skeleton required by the task *)
INIT == TRUE
NEXT == TRUE
SPECIFICATION == INIT /\ [][NEXT]_<<>>
INVARIANTS == TRUE
PROPERTIES == TRUE

====