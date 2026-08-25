---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT NULL

(* 1. Set overlap test: true iff S and T share at least one element *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum and minimum element selection from a set *)
SetMax(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S : \A y \in S : x <= y

RECURSIVE SetReduce, SeqReduce, IndexOf, RemoveAll, Permutations

(* 3. Generalized set reduction (fold over a set) *)
SetReduce(S, acc, f) ==
    IF S = {} THEN acc
    ELSE
        LET x == CHOOSE y \in S : TRUE IN
        SetReduce(S \ {x}, f(acc, x), f)

(* 4. Sequence reduction (fold over a sequence) *)
SeqReduce(seq, acc, f) ==
    IF Len(seq) = 0 THEN acc
    ELSE
        LET x == seq[1] IN
        SeqReduce( Tail(seq), f(acc, x), f)

(* 5. Index of the first occurrence of an element in a sequence (0 if absent) *)
IndexOf(seq, e) ==
    IF e \notin seq THEN 0
    ELSE
        CHOOSE i \in 1..Len(seq) :
            /\ seq[i] = e
            /\ \A j \in 1..(i - 1) : seq[j] # e

(* 6. Convert a sequence to the set of its elements *)
SeqToSet(seq) == { x : \E i \in 1..Len(seq) : seq[i] = x }

(* 7. Last element of a sequence (NULL if empty) *)
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* 8. Test if a sequence is empty *)
IsEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence *)
RemoveAll(seq, e) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE
        LET x == seq[1] IN
        IF x = e THEN RemoveAll( Tail(seq), e )
        ELSE <<x>> \o RemoveAll( Tail(seq), e )

(* 10. Intersection of a set of sets *)
SetIntersection(SS) == IF SS = {} THEN {} ELSE \cap SS

(* 11. Generate all permutation sequences of a finite set *)
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE
        UNION { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

(* 12. Test helper that prints a diagnostic message on failure *)
TestHelper(cond, msg) ==
    IF cond THEN TRUE
    ELSE Print(msg) /\ FALSE

====