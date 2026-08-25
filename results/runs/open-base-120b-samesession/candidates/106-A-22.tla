---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Utility operators
   ---------------------------------------------------------------------- *)

(* 1. Set intersection test (whether two sets overlap) *)
Overlaps(S, T) == \E x \in S : x \in T

(* 2. Maximum and minimum element selection from a set *)
MaxSet(S) == IF S = {} THEN NULL
            ELSE CHOOSE x \in S : \A y \in S : y <= x

MinSet(S) == IF S = {} THEN NULL
            ELSE CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold over a set with an accumulator) *)
RECURSIVE SetReduce(_,_,_)
SetReduce(S, acc, f) ==
  IF S = {} THEN acc
  ELSE LET a == CHOOSE x \in S : TRUE
       IN SetReduce(S \ {a}, f(acc, a), f)

(* 4. Sequence reduction (fold over a sequence with an accumulator) *)
SeqReduce(seq, acc, f) == Fold(seq, acc, f)

(* 5. Finding the index of an element in a sequence (1‑based, 0 if absent) *)
IndexOf(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem
  THEN CHOOSE i \in 1..Len(seq) :
        /\ seq[i] = elem
        /\ \A j \in 1..i-1 : seq[j] # elem
  ELSE 0

(* 6. Converting a sequence to the set of its elements *)
SeqToSet(seq) == { e : \E i \in 1..Len(seq) : seq[i] = e }

(* 7. Getting the last element of a sequence *)
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 8. Testing if a sequence is empty *)
IsEmpty(seq) == Len(seq) = 0

(* 9. Removing all occurrences of an element from a sequence *)
RemoveAll(seq, elem) == SeqFilter(seq, LAMBDA x : x # elem)

(* 10. Computing the intersection of a set of sets *)
SetIntersection(S) == INTERSECTION S

(* 11. Generating all permutation sequences of a finite set *)
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE UNION { <<e>> \o p :
                e \in S,
                p \in Permutations(S \ {e}) }

(* 12. Test helper that prints diagnostic information on failure *)
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE (Print(msg) ; FALSE)

(* ----------------------------------------------------------------------
   Dummy specification placeholders (required identifiers)
   ---------------------------------------------------------------------- *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====