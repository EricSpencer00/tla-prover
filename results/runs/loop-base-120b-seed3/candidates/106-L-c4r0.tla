---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(* ----------------------------------------------------------------------
   Utility operators
   ---------------------------------------------------------------------- *)

(* 1. Set intersection test (whether two sets overlap) *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum element selection from a set *)
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x

(* 2. Minimum element selection from a set *)
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold over a set with an accumulator) *)
SetReduce(S, f, a) ==
    IF S = {} THEN a
    ELSE
        LET e == CHOOSE x \in S : TRUE
        IN SetReduce(S \ {e}, f, f(a, e))

(* 4. Sequence reduction (fold over a sequence with an accumulator) *)
SeqReduce(seq, f, a) == FoldSeq(seq, a, f)

(* 5. Finding the index of an element in a sequence *)
SeqIndex(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

(* 6. Converting a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Getting the last element of a sequence *)
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 8. Testing if a sequence is empty *)
IsEmpty(seq) == Len(seq) = 0

(* 9. Removing all occurrences of an element from a sequence *)
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF seq[1] = elem
         THEN RemoveAll(Tail(seq), elem)
         ELSE << seq[1] >> \o RemoveAll(Tail(seq), elem)

(* 10. Computing the intersection of a set of sets *)
SetIntersectionOfSets(S) ==
    IF S = {} THEN {}
    ELSE { x : \A Y \in S : x \in Y }

(* 11. Generating all permutation sequences of a finite set *)
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 12. Test helper for writing assertions that print diagnostics on failure *)
TestHelper(expr, msg) ==
    IF expr THEN TRUE ELSE (Print(msg) /\ FALSE)

(* ----------------------------------------------------------------------
   Specification scaffolding (no state)
   ---------------------------------------------------------------------- *)

INIT == TRUE

NEXT == UNCHANGED <<>>

SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == {}

PROPERTIES == {}

====