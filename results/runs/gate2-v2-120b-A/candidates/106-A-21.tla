---- MODULE Util ----
EXTENDS Sequences, TLC

CONSTANTS
    \* No constants are required for this utility module, but we declare the
    \* name to satisfy the requirement that every identifier listed in the
    \* .cfg file be present.  The constant may be instantiated arbitrarily in
    \* the .cfg file.
    Util

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

(* 1. Set intersection test: returns TRUE iff the two sets overlap. *)
SetIntersectionTest(A, B) == \E x \in A : x \in B

(* 2. Maximum element of a non‑empty finite set. *)
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

(* 2. Minimum element of a non‑empty finite set. *)
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold) over a finite set. *)
SetFold(A, op, acc) ==
    IF A = {} THEN acc
    ELSE LET x == CHOOSE y \in A : TRUE IN
         SetFold(A \ {x}, op, op(acc, x))

(* 4. Sequence reduction (fold) using the library operator. *)
SeqFold(seq, op, acc) == Fold(seq, op, acc)

(* 5. Index of an element in a sequence, or 0 if not present. *)
SeqIndex(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

(* 6. Convert a sequence to the set of its elements. *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Last element of a non‑empty sequence. *)
SeqLast(seq) == seq[Len(seq)]

(* 8. Test whether a sequence is empty. *)
SeqEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of an element from a sequence. *)
SeqRemoveAll(seq, elem) ==
    [i \in 1..(Len(seq) - Cardinality({j \in 1..Len(seq) : seq[j] = elem}))) |-> 
        seq[ (CHOOSE k \in 1..Len(seq) :
                seq[k] # elem /\ 
                Cardinality({j \in 1..k : seq[j] # elem}) = i))]

(* 10. Intersection of a set of sets. *)
SetOfSetsIntersection(F) ==
    IF F = {} THEN {}
    ELSE /\ \A S \in F : S \subseteq UNION F
         /\ \A x \in UNION F : x \in { y \in UNION F : \A S \in F : y \in S }

(* 11. Generate all permutations of a finite set. *)
Permutations(F) ==
    IF F = {} THEN { <<>> }
    ELSE { <<x>> \o rest : x \in F, rest \in Permutations(F \ {x}) }

(* 12. Test helper that fails with a diagnostic message. *)
Assert(pred, msg) ==
    IF pred THEN TRUE
    ELSE BEGIN Print("Assertion failed: " \o msg); FALSE END

=============================================================================