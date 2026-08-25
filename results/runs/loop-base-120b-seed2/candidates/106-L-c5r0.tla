---- MODULE Util ----
EXTENDS Naturals, Sequences

(*--- Specification scaffold (no state variables) ---*)
Init == TRUE
Next == TRUE
SPECIFICATION == Init /\ [][Next]_<<>>

INVARIANTS == TRUE
PROPERTIES == TRUE

(*--- Utility operators ---*)

(* 1. Set overlap test (whether two sets intersect) *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum and minimum element selection from a set *)
Max(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S : \A y \in S : y <= x
Min(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold over a set) *)
RECURSIVE SetReduce(_,_ ,_)
SetReduce(S, f, a) ==
  IF S = {} THEN a
  ELSE
    LET x == CHOOSE e \in S : TRUE
    IN SetReduce(S \ {x}, f, f(x, a))

(* 4. Sequence reduction (fold over a sequence) *)
RECURSIVE SeqReduce(_,_ ,_)
SeqReduce(seq, f, a) ==
  IF Len(seq) = 0 THEN a
  ELSE SeqReduce(SeqTail(seq), f, f(Head(seq), a))

(* 5. Index of an element in a sequence (returns 0 if not present) *)
IndexOf(seq, e) ==
  IF \E i \in 1..Len(seq) : seq[i] = e
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = e
    ELSE 0

(* 6. Convert a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Last element of a sequence (NULL if empty) *)
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 8. Test whether a sequence is empty *)
IsSeqEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence *)
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = e
       THEN RemoveAll(SeqTail(seq), e)
       ELSE <<Head(seq)>> \o RemoveAll(SeqTail(seq), e)

(* 10. Intersection of a set of sets *)
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE { x : \A S \in SS : x \in S }

(* 11. All permutations of a finite set *)
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { { <<e>> \o p : p \in Permutations(S \ {e}) } : e \in S }

(* 12. Assertion helper that prints diagnostic info on failure *)
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE
    LET _ == Print(msg) IN FALSE

====