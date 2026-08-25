---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

(* 1. Set intersection test (whether two sets overlap) *)
Overlap(S, T) == \E x \in S : x \in T

(* 2. Maximum and minimum element selection from a (non‑empty) set *)
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : y >= x

(* 3. Generalized set reduction (fold over a set with an accumulator) *)
RECURSIVE SetReduce(_,_,_)
SetReduce(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET e == CHOOSE x \in S : TRUE
    IN SetReduce(S \ {e}, f(acc, e), f)

(* 4. Sequence reduction (fold over a sequence with an accumulator) *)
SeqReduce(seq, acc, f) == FoldSeq(f, acc, seq)

(* 5. Finding the index of an element in a sequence (1‑based, 0 if absent) *)
IndexOf(seq, elem) ==
  IF elem \in SeqSet(seq) THEN SeqPos(seq, elem) ELSE 0

(* 6. Converting a sequence to the set of its elements *)
SeqSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Getting the last element of a sequence *)
Last(seq) ==
  IF Len(seq) = 0 THEN <<>> ELSE seq[Len(seq)]

(* 8. Testing if a sequence is empty *)
IsEmpty(seq) == Len(seq) = 0

(* 9. Removing all occurrences of an element from a sequence *)
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem
       THEN RemoveAll(Tail(seq), elem)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

(* 10. Computing the intersection of a set of sets *)
SetIntersection(sets) ==
  IF sets = {} THEN {}
  ELSE
    LET first == CHOOSE s \in sets : TRUE
    IN { x \in first : \A s \in sets : x \in s }

(* 11. Generating all permutation sequences of a finite set *)
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE
    UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 12. Test helper that prints diagnostic information on failure *)
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE (Print(msg) = msg) /\ FALSE

=============================================================================