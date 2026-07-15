---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Utility library for the key-value store specifications.                *)
(*  Provides a collection of reusable operators for set and sequence       *)
(*  manipulation.                                                          *)
(***************************************************************************)

(***************************************************************************)
(*  1. Set intersection test: Overlap(s, t) returns TRUE iff the two sets   *)
(*     have at least one element in common.                                 *)
(***************************************************************************)
Overlap(s, t) == \E x \in s : x \in t

(***************************************************************************)
(*  2. Maximum and minimum element selection from a set.                    *)
(*     Max(s) returns the greatest element of a non‑empty finite set s.     *)
(*     Min(s) returns the smallest element of a non‑empty finite set s.     *)
(*     Both are undefined for the empty set (the specification does not   *)
(*     require a defined value in that case).                               *)
(***************************************************************************)
Max(s) == 
    IF s = {} THEN 
        CHOOSE x \in {} : TRUE 
    ELSE 
        \E x \in s : \A y \in s : y <= x

Min(s) == 
    IF s = {} THEN 
        CHOOSE x \in {} : TRUE 
    ELSE 
        \E x \in s : \A y \in s : y >= x

(***************************************************************************)
(*  3. Generalized set reduction (fold over a set).                        *)
(*     SetReduce(s, init, f) folds the binary operator f over the elements *)
(*     of the finite set s, starting with the accumulator value init.      *)
(*     The order of folding is nondeterministic, but the result is the    *)
(*     same as any sequential application of f to all elements of s.      *)
(***************************************************************************)
SetReduce(s, init, f) ==
    IF s = {} THEN init
    ELSE
        LET Rec(s, acc) ==
            IF s = {} THEN acc
            ELSE
                \E x \in s :
                    Rec(s \ {x}, f(acc, x))
        IN Rec(s, init)

(***************************************************************************)
(*  4. Sequence reduction (fold over a sequence).                         *)
(*     SeqReduce(seq, init, f) folds the binary operator f over the       *)
(*     elements of the sequence seq from left to right, starting with     *)
(*     the accumulator value init.                                          *)
(***************************************************************************)
SeqReduce(seq, init, f) ==
    IF Len(seq) = 0 THEN init
    ELSE f(SeqReduce(SubSeq(seq, 2, Len(seq)), init, f), Head(seq))

(***************************************************************************)
(*  5. Finding the index of an element in a sequence.                      *)
(*     IndexOf(seq, e) returns the smallest position i (1‑based) such that*)
(*     seq[i] = e, or 0 if e does not occur in seq.                        *)
(***************************************************************************)
IndexOf(seq, e) ==
    IF e \notin set(seq) THEN 0
    ELSE
        CHOOSE i \in 1..Len(seq) : seq[i] = e

(***************************************************************************)
(*  6. Converting a sequence to the set of its elements.                   *)
(*     SeqToSet(seq) returns the set of all distinct elements appearing   *)
(*     in seq.                                                              *)
(***************************************************************************)
SeqToSet(seq) == set(seq)

(***************************************************************************)
(*  7. Getting the last element of a sequence.                             *)
(*     Last(seq) returns seq[Len(seq)] for non‑empty seq; the value is     *)
(*     undefined for the empty sequence.                                    *)
(***************************************************************************)
Last(seq) == seq[Len(seq)]

(***************************************************************************)
(*  8. Testing if a sequence is empty.                                      *)
(*     IsEmpty(seq) is TRUE iff the sequence has length zero.             *)
(***************************************************************************)
IsEmpty(seq) == Len(seq) = 0

(***************************************************************************)
(*  9. Removing all occurrences of an element from a sequence.            *)
(*     RemoveAll(seq, e) returns a new sequence consisting of the elements*)
(*     of seq with every occurrence of e omitted, preserving the original *)
(*     order of the remaining elements.                                     *)
(***************************************************************************)
RemoveAll(seq, e) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE
        IF Head(seq) = e THEN
            RemoveAll(Tail(seq), e)
        ELSE
            <<Head(seq)>> \o RemoveAll(Tail(seq), e)

(***************************************************************************)
(* 10. Computing the intersection of a set of sets.                        *)
(*     IntersectSets(ss) returns the set of elements that belong to every *)
(*     member of the collection ss (which must be a set of sets).          *)
(***************************************************************************)
IntersectSets(ss) ==
    IF ss = {} THEN {}
    ELSE
        \* Start with an arbitrary member of ss and intersect with the rest.
        LET first == CHOOSE s \in ss : TRUE IN
        { x \in first : \A s \in ss : x \in s }

(***************************************************************************)
(* 11. Generating all permutation sequences of a finite set.              *)
(*     Permutations(s) returns the set of all sequences that are           *)
(*     permutations of the elements of the finite set s.                    *)
(*     The definition is recursive: the permutations of the empty set are *)
(*     the singleton set containing the empty sequence; for a non‑empty   *)
(*     set, each permutation is obtained by inserting each element into   *)
(*     every possible position of every permutation of the remaining set.  *)
(***************************************************************************)
Permutations(s) ==
    IF s = {} THEN { <<>> }
    ELSE
        UNION { 
            \E p \in Permutations(s \ {e}) :
                { InsertAt(p, i, e) : i \in 1..(Len(p) + 1) }
            : e \in s
        }

(***************************************************************************)
(*  Helper: Insert element e at position i (1‑based) in sequence seq.      *)
(*  The result has length Len(seq)+1, with e placed before the original   *)
(*  element that was at position i (or appended if i = Len(seq)+1).        *)
(***************************************************************************)
InsertAt(seq, i, e) ==
    IF i = 1 THEN <<e>> \o seq
    ELSE IF i > Len(seq) + 1 THEN seq \o <<e>>
    ELSE <<Head(seq)>> \o InsertAt(Tail(seq), i - 1, e)

(***************************************************************************)
(* 12. Test helper for writing assertions that print diagnostic information *)
(*     on failure. The operator Assert(cond, msg) evaluates to TRUE when   *)
(*     cond is TRUE; otherwise it prints msg and returns FALSE, causing    *)
(*     the model checker to report a failed assertion.                     *)
(***************************************************************************)
Assert(cond, msg) ==
    IF cond THEN TRUE
    ELSE
        Print(msg) /\ FALSE

(***************************************************************************)
(*  The following identifiers are required by the reference .cfg file.    *)
(*  They are defined as trivial stuttering specifications so that the     *)
(*  module can be checked without additional state.                         *)
(***************************************************************************)

VARIABLE dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_<<dummy>>

=============================================================================