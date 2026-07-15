---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Utility operators for set and sequence manipulation
   ---------------------------------------------------------------------- *)

(* 1. Set intersection test: do two sets overlap? *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum element of a non‑empty finite set of naturals *)
SetMax(S) == 
    IF S = {} THEN 0
    ELSE CHOOSE x \in S : \A y \in S : y <= x

(* 2. Minimum element of a non‑empty finite set of naturals *)
SetMin(S) == 
    IF S = {} THEN 0
    ELSE CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold over a set) *)
SetReduce(Fun, Init, S) ==
    IF S = {} THEN Init
    ELSE
        LET x == CHOOSE y \in S : TRUE IN
        SetReduce(Fun, Fun(Init, x), S \ {x})

(* 4. Sequence reduction (fold over a sequence) using library FoldSeq *)
SeqReduce(Fun, Init, seq) == FoldSeq(Fun, Init, seq)

(* 5. Index of the first occurrence of an element in a sequence *)
SeqIndex(s, el) ==
    IF \E i \in 1..Len(s) : s[i] = el
    THEN 1 + \A i \in 1..Len(s) :
            (s[i] # el) => (SeqIndex(SubSeq(s, i+1, Len(s)), el) = i-1)
    ELSE -1

(* 6. Convert a sequence to the set of its elements *)
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

(* 7. Last element of a non‑empty sequence *)
SeqLast(s) == s[Len(s)]

(* 8. Test if a sequence is empty *)
SeqIsEmpty(s) == Len(s) = 0

(* 9. Remove all occurrences of an element from a sequence *)
SeqRemoveAll(s, el) ==
    [ i \in 1..Len(s) |-> 
        IF s[i] = el THEN @ ELSE s[i] ]
    \* The above preserves positions; we compress the result:
    [ i \in 1..Cardinality({ j \in 1..Len(s) : s[j] # el }) |-> 
        s[CHOOSE j \in 1..Len(s) : 
            s[j] # el /\ 
            Cardinality({ k \in 1..j : s[k] # el }) = i) ]

(* 10. Intersection of a set of sets *)
SetIntersectionOfSets(SS) ==
    IF SS = {} THEN {}
    ELSE \Inter SS

(* 11. Generate all permutations of a finite set of naturals *)
Permutations(S) ==
    IF S = {} THEN { << >> }
    ELSE
        UNION { 
            [seq \in Permutations(S \ {x}) |-> <<x>> \o seq] : x \in S
        }

(* 12. Test helper that prints a message on failure *)
Assert(msg, pred) ==
    IF pred THEN TRUE ELSE 
        Print("ASSERTION FAILED: " \o msg) /\ FALSE

=============================================================================