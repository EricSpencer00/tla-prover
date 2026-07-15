---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Utility library for the KV store project.
  Provides a collection of helper operators.
-----------------------------------------------------------------*)

(* ---------------------------- Constants ---------------------------- *)
(* No constants are required for this module. *)

(* ---------------------------- Operators ---------------------------- *)

(* 1. Set intersection test: returns TRUE iff the two sets overlap. *)
Overlap(S, T) == \E x \in S : x \in T

(* 2. Maximum element of a non‑empty set of naturals.
   Returns the greatest element; it's undefined for the empty set. *)
Max(S) == 
    IF S = {} THEN 
        CHOOSE x \in Nat : FALSE (* undefined; will not be used on empty set *)
    ELSE 
        MaxAux(S, 0)

(* Helper for Max: iterates through elements and keeps the greatest seen. *)
MaxAux(S, cur) == 
    IF \A x \in S : x <= cur THEN cur
    ELSE 
        \E y \in S : y > cur /\ MaxAux(S, y)

(* 3. Minimum element of a non‑empty set of naturals. *)
Min(S) == 
    IF S = {} THEN 
        CHOOSE x \in Nat : FALSE
    ELSE 
        MinAux(S, CHOOSE y \in S : TRUE) \* pick any element as initial

MinAux(S, cur) == 
    IF \A x \in S : x >= cur THEN cur
    ELSE 
        \E y \in S : y < cur /\ MinAux(S, y)

(* 4. Generalized set reduction (fold) using a binary operator Op. *)
SetFold(<<>>, Op, acc) == acc
SetFold(S, Op, acc) == 
    LET x == CHOOSE y \in S : TRUE IN
    SetFold(S \ {x}, Op, Op(acc, x))

(* 5. Sequence reduction (fold) using the library SeqFold. *)
SeqFold(seq, Op, acc) == 
    IF Len(seq) = 0 THEN acc
    ELSE SeqFold(Tail(seq), Op, Op(acc, Head(seq)))

(* 6. Index of element e in a sequence seq (1‑based). Returns 0 if not found. *)
SeqIndex(seq, e) == 
    IF e \notin set(seq) THEN 0
    ELSE 
        CHOOSE i \in 1..Len(seq) : seq[i] = e

(* 7. Convert a sequence to the set of its elements. *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 8. Last element of a non‑empty sequence. *)
Last(seq) == 
    IF Len(seq) = 0 THEN 
        CHOOSE x \in Nat : FALSE
    ELSE seq[Len(seq)]

(* 9. Empty‑sequence test. *)
SeqEmpty(seq) == Len(seq) = 0

(* 10. Remove all occurrences of element e from sequence seq. *)
SeqRemove(seq, e) == 
    IF Len(seq) = 0 THEN <<>>
    ELSE 
        IF Head(seq) = e THEN SeqRemove(Tail(seq), e)
        ELSE <<Head(seq)>> \o SeqRemove(Tail(seq), e)

(* 11. Intersection of a set of sets. Returns the common elements. *)
SetIntersection(SS) == 
    IF SS = {} THEN {}
    ELSE 
        \cap_{S \in SS} S

(* 12. Generate all permutations of a finite set S (as sequences). *)
AllPermutations(S) == 
    IF S = {} THEN {<<>>}
    ELSE 
        { <<x>> \o p : x \in S, p \in AllPermutations(S \ {x}) }

(* 13. Test helper that asserts a condition and prints a message on failure. *)
Assert(cond, msg) == 
    IF cond THEN TRUE
    ELSE 
        BEGIN 
            Print(msg);
            FALSE
        END

(* ---------------------------- Spec skeleton ---------------------------- *)

(* Even though this module is a library, we provide the required skeleton
   identifiers so that the reference .cfg can refer to them without error. *)

VARIABLE dummy

(* SPECIFICATION: the overall spec name (required by the cfg). *)
Spec == Init /\ []Next

(* INIT: a trivial initial predicate. *)
Init == dummy \in {0}

(* NEXT: a trivial stuttering step. *)
Next == dummy' = dummy

(* INVARIANTS: a set containing a single trivial invariant. *)
INVARIANTS == { TypeOK }

(* A basic type‑correctness invariant for the dummy variable. *)
TypeOK == dummy \in {0}

(* PROPERTIES: a set containing a single trivial liveness property. *)
PROPERTIES == { Liveness }

(* A trivial liveness property (always eventually true). *)
Liveness == <>TRUE

====