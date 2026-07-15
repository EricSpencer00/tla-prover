---- MODULE Util ----
EXTENDS FiniteSets, Sequences, TLC

(***************************************************************************)
(* Utility library for reusable operators                                 *)
(* Provides common helpers for set and sequence manipulation               *)
(***************************************************************************)

(***************************************************************************)
(* 1. Set intersection test: Overlap(s, t) returns TRUE iff s ∩ t ≠ ∅      *)
(***************************************************************************)
Overlap(s, t) == \E x \in s : x \in t

(***************************************************************************)
(* 2. Maximum and minimum element selection from a finite, non‑empty set   *)
(***************************************************************************)
SetMax(s) == 
    IF s = {} THEN 
        NULL 
    ELSE 
        CHOOSE x \in s : \A y \in s : y <= x

SetMin(s) == 
    IF s = {} THEN 
        NULL 
    ELSE 
        CHOOSE x \in s : \A y \in s : x <= y

(***************************************************************************)
(* 3. Generalized set reduction (fold over a set with an accumulator)     *)
(*    SetReduce(s, op, acc) folds op over the elements of s in an         *)
(*    arbitrary order, starting with accumulator acc.                     *)
(***************************************************************************)
SetFold(s, op, acc) == 
    IF s = {} THEN 
        acc 
    ELSE 
        LET x == CHOOSE y \in s : TRUE 
        IN SetFold(s \ {x}, op, op(acc, x))

(* Alias matching the description name *)
SetReduce(s, op, acc) == SetFold(s, op, acc)

(***************************************************************************)
(* 4. Sequence reduction (fold over a sequence with an accumulator)       *)
(*    SeqReduce(seq, op, acc) folds op left‑to‑right over seq.            *)
(***************************************************************************)
SeqReduce(seq, op, acc) == 
    IF seq = <<>> THEN 
        acc 
    ELSE 
        SeqReduce(Tail(seq), op, op(acc, Head(seq)))

(***************************************************************************)
(* 5. IndexOf(seq, elem) returns the 1‑based index of elem in seq, or 0    *)
(*    if elem does not occur.                                            *)
(***************************************************************************)
IndexOf(seq, elem) == 
    IF elem \in set(seq) THEN 
        Card({ i \in 1..Len(seq) : seq[i] = elem })
    ELSE 0

(***************************************************************************)
(* 6. SetFromSeq(seq) returns the set of elements occurring in seq.       *)
(***************************************************************************)
SetFromSeq(seq) == set(seq)

(***************************************************************************)
(* 7. Last(seq) returns the last element of a non‑empty sequence.         *)
(*    For the empty sequence it returns NULL.                             *)
(***************************************************************************)
Last(seq) == 
    IF Len(seq) = 0 THEN 
        NULL 
    ELSE 
        seq[Len(seq)]

(***************************************************************************)
(* 8. IsEmptySeq(seq) tests whether a sequence is empty.                  *)
(***************************************************************************)
IsEmptySeq(seq) == Len(seq) = 0

(***************************************************************************)
(* 9. RemoveAll(seq, elem) returns seq with every occurrence of elem       *)
(*    removed.                                                            *)
(***************************************************************************)
RemoveAll(seq, elem) == 
    IF Len(seq) = 0 THEN 
        <<>> 
    ELSE 
        IF Head(seq) = elem THEN 
            RemoveAll(Tail(seq), elem) 
        ELSE 
            <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

(***************************************************************************)
(* 10. IntersectSets(ss) computes the intersection of a set of sets.      *)
(*     The argument ss is a set whose elements are themselves sets.       *)
(***************************************************************************)
IntersectSets(ss) == 
    IF ss = {} THEN {} 
    ELSE 
        \E s \in ss : 
            /\ s = {} => {} 
            /\ s # {} => 
                CHOOSE x \in s : 
                    \A t \in ss : x \in t

(* A more direct definition using recursion *)
(* IntersectSets(ss) == 
    IF ss = {} THEN {} 
    ELSE 
        /\ \A t \in ss : t # {} 
        /\ { x \in UNION ss : \A t \in ss : x \in t } *)

(***************************************************************************)
(* 11. Permutations(s) returns the set of all finite sequences that are    *)
(*     permutations of the elements of the finite set s.                  *)
(***************************************************************************)
Permutations(s) == 
    IF s = {} THEN { <<>> } 
    ELSE 
        { <<x>> \o p : x \in s, 
                        p \in Permutations(s \ {x}) }

(***************************************************************************)
(* 12. AssertHelper(cond, msg) is a helper for writing assertions that    *)
(*     print diagnostic information on failure.                           *)
(***************************************************************************)
AssertHelper(cond, msg) == 
    IF cond THEN TRUE 
    ELSE PrintT(msg) /\ FALSE

(***************************************************************************)
(* The following names are required by the reference .cfg but are not    *)
(* used in this purely functional library. They are defined as stubs.    *)
(***************************************************************************)

(*** SPECIFICATION, INIT, NEXT, INVARIANTS, PROPERTIES are intentionally *) 
(*** left undefined because the library provides no state machine.     ***)

(***************************************************************************)
(* End of Util module                                                    *)
(***************************************************************************)
====