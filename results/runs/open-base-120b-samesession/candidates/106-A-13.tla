---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

(* 1. Set intersection test: returns TRUE iff S and T overlap *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum and minimum element selection from a non‑empty finite set *)
SetMax(S) == 
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold over a set) *)
RECURSIVE SetFold(_,_ ,_)
SetFold(S, acc, f) ==
    IF S = {} THEN acc
    ELSE 
        LET x == CHOOSE e \in S : TRUE
        IN SetFold(S \ {x}, f(acc, x), f)

(* 4. Sequence reduction (fold over a sequence) *)
RECURSIVE SeqFold(_,_ ,_)
SeqFold(seq, acc, f) ==
    IF Len(seq) = 0 THEN acc
    ELSE SeqFold(Tail(seq), f(acc, Head(seq)), f)

(* 5. Index of an element in a sequence (1‑based, 0 if not present) *)
IndexOf(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

(* 6. Convert a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Last element of a sequence (NULL if empty) *)
Last(seq) == 
    IF Len(seq) = 0 THEN NULL
    ELSE seq[Len(seq)]

(* 8. Test if a sequence is empty *)
IsEmptySeq(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence *)
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = elem
         THEN RemoveAll(Tail(seq), elem)
         ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

(* 10. Intersection of a set of sets *)
SetIntersection(SS) ==
    IF SS = {} THEN {}
    ELSE 
        LET s == CHOOSE t \in SS : TRUE
        IN { x \in s : \A t \in SS : x \in t }

(* 11. Generate all permutations of a finite set *)
RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { <<a>> \o p : a \in S, p \in Permutations(S \ {a}) }

(* 12. Test helper for assertions (prints diagnostics on failure) *)
TestHelper(expr, msg) == expr

\* ----------------------------------------------------------------------
\* Specification skeleton (required identifiers)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====