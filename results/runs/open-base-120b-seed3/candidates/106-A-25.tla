---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Utility operators for set and sequence manipulation                    *)
(***************************************************************************)

(* 1. Set intersection test: whether two sets overlap *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum and minimum element selection from a set *)
SetMax(S) == 
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : y >= x

(* 3. Generalized set reduction (fold over a set with an accumulator) *)
SetReduce(S, init, f) == 
    LET Rec(set) == 
        IF set = {} THEN init
        ELSE 
            LET e == CHOOSE x \in set
            IN f(e, Rec(set \ {e}))
    IN Rec(S)

(* 4. Sequence reduction (fold over a sequence with an accumulator) *)
SeqReduce(seq, init, f) == 
    IF Len(seq) = 0 THEN init
    ELSE f(Head(seq), SeqReduce(Tail(seq), init, f))

(* 5. Finding the index of an element in a sequence (1‑based, 0 if absent) *)
SeqIndex(seq, elem) == 
    IF Len(seq) = 0 THEN 0
    ELSE IF Head(seq) = elem THEN 1
    ELSE 
        LET restIdx == SeqIndex(Tail(seq), elem) IN
            IF restIdx = 0 THEN 0 ELSE 1 + restIdx

(* 6. Converting a sequence to the set of its elements *)
SeqToSet(seq) == { x : \E i \in 1..Len(seq) : seq[i] = x }

(* 7. Getting the last element of a sequence *)
SeqLast(seq) == 
    IF Len(seq) = 0 THEN NULL
    ELSE seq[Len(seq)]

(* 8. Testing if a sequence is empty *)
SeqIsEmpty(seq) == Len(seq) = 0

(* 9. Removing all occurrences of an element from a sequence *)
SeqRemoveAll(seq, elem) == 
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = elem THEN SeqRemoveAll(Tail(seq), elem)
    ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

(* 10. Computing the intersection of a set of sets *)
SetIntersectionOfSets(SS) == 
    IF SS = {} THEN {}
    ELSE \cap SS

(* 11. Generating all permutation sequences of a finite set *)
Permutations(S) == 
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 12. Test helper for writing assertions that print diagnostic information *)
TestHelper(expr, msg) == 
    IF expr THEN TRUE
    ELSE (Print(msg); FALSE)

(***************************************************************************)
(* Stubs required by the reference configuration                           *)
(***************************************************************************)

SPECIFICATION == TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == {}

PROPERTIES == {}

====