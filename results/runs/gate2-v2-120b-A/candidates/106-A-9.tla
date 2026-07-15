---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*
  Utility library for key-value store specifications.
  Provides a collection of pure operators for set and sequence manipulation.
*)

(* ------------------------------------------------------------------- *)
(* 1. Set intersection test: Overlap(s, t) = TRUE iff s and t share an element *)
Overlap(s, t) == \E x \in s : x \in t

(* 2. Maximum and minimum element selection from a non‑empty set *)
Max(S) == 
    IF S = {} THEN {} 
    ELSE LET m == CHOOSE x \in S : \A y \in S : y <= x IN m

Min(S) == 
    IF S = {} THEN {} 
    ELSE LET m == CHOOSE x \in S : \A y \in S : x <= y IN m

(* 3. Generalized set reduction (fold) *)
SetFold(op, init, S) ==
    IF S = {} THEN init
    ELSE 
        LET Rec == [set |-> {}] IN
        RECURSIVE Rec(_)
        Rec(set) ==
            IF set = {} THEN init
            ELSE 
                LET x == CHOOSE y \in set : TRUE IN
                op(x, Rec(set \ {x}))
        IN Rec(S)

(* 4. Sequence reduction (fold) using the built‑in FoldSeq operator *)
SeqFold(op, init, seq) ==
    FoldSeq(op, init, seq)

(* 5. Find the (1‑based) index of an element in a sequence, or 0 if absent *)
Index(seq, elem) ==
    IF elem \in {seq[i] : i \in DOMAIN seq}
       THEN Min({ i \in DOMAIN seq : seq[i] = elem })
       ELSE 0

(* 6. Convert a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

(* 7. Get the last element of a non‑empty sequence *)
Last(seq) ==
    IF seq = <<>> THEN {}
    ELSE seq[ Len(seq) ]

(* 8. Test if a sequence is empty *)
SeqEmpty(seq) == seq = <<>>

(* 9. Remove all occurrences of an element from a sequence *)
SeqRemove(seq, elem) ==
    << seq[i] : i \in DOMAIN seq /\ seq[i] # elem >>

(* 10. Intersection of a set of sets (must be non‑empty) *)
SetIntersection(setOfSets) ==
    IF setOfSets = {} THEN {}
    ELSE /\ \A X \in setOfSets : X # {}
         /\ \E x \in UNION setOfSets :
                \A X \in setOfSets : x \in X
         /\ { x \in UNION setOfSets :
                \A X \in setOfSets : x \in X }

(* 11. Generate all permutations of a finite set *)
PermutationSequences(S) ==
    IF S = {} THEN { <<>> }
    ELSE
        UNION { << e >> \o p :
                    e \in S,
                    p \in PermutationSequences(S \ {e}) }

(* 12. Test helper that asserts a condition and prints a message on failure *)
Assert(cond, msg) ==
    IF cond THEN TRUE
    ELSE /\ FALSE
         /\ Print(msg)

=============================================================================