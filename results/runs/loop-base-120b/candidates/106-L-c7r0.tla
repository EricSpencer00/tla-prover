---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

(* ----------------------------------------------------------------------
   Utility operators
   ---------------------------------------------------------------------- *)

(* 1. Set intersection test (whether two sets overlap) *)
SetOverlap(S, T) == S \cap T # {}

(* 2. Maximum and minimum element selection from a set *)
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold over a set with an accumulator) *)
SetReduce(S, a, f) ==
    IF S = {} THEN a
    ELSE
        LET x == CHOOSE e \in S
        IN SetReduce(S \ {x}, f(a, x), f)

(* 4. Sequence reduction (fold over a sequence with an accumulator) *)
SeqReduce(seq, a, f) == FoldSeq(seq, f, a)

(* 5. Finding the index of an element in a sequence (1‑based, 0 if not found) *)
SeqIndex(seq, elem) ==
    IF seq = <<>> THEN 0
    ELSE IF Head(seq) = elem THEN 1
    ELSE
        LET idx == SeqIndex(Tail(seq), elem)
        IN IF idx = 0 THEN 0 ELSE idx + 1

(* 6. Converting a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Getting the last element of a sequence *)
SeqLast(seq) ==
    IF seq = <<>> THEN NULL
    ELSE seq[Len(seq)]

(* 8. Testing if a sequence is empty *)
SeqIsEmpty(seq) == seq = <<>>

(* 9. Removing all occurrences of an element from a sequence *)
SeqRemoveAll(seq, elem) ==
    IF seq = <<>> THEN <<>>
    ELSE IF Head(seq) = elem THEN SeqRemoveAll(Tail(seq), elem)
    ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

(* 10. Computing the intersection of a set of sets *)
SetIntersectionOfSets(S) ==
    IF S = {} THEN {}
    ELSE
        LET s == CHOOSE t \in S
        IN s \cap SetIntersectionOfSets(S \ {s})

(* 11. Generating all permutation sequences of a finite set *)
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE
        UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 12. Test helper for writing assertions that print diagnostic information on failure *)
TestHelper(cond, msg) ==
    IF cond THEN TRUE ELSE (Print(msg) /\ FALSE)

(* ----------------------------------------------------------------------
   Specification placeholders required by the task
   ---------------------------------------------------------------------- *)

SPECIFICATION == TRUE

INIT == TRUE

NEXT == UNCHANGED <<>>

INVARIANTS == {}

PROPERTIES == {}

====