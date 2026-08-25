---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Utility operators for set and sequence manipulation                    *)
(***************************************************************************)

(* 1. Set overlap test: returns TRUE iff two sets have a common element. *)
SetOverlap(S, T) == \E x \in S : x \in T

(* 2. Maximum and minimum element selection from a (possibly empty) set. *)
Null == "NULL"

Max(S) ==
  IF S = {} THEN Null
  ELSE CHOOSE x \in S : \A y \in S : y <= x

Min(S) ==
  IF S = {} THEN Null
  ELSE CHOOSE x \in S : \A y \in S : y >= x

(* 3. Convert a sequence to the set of its elements. *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 4. Index of an element in a sequence (1‑based, 0 if absent). *)
IndexOf(seq, e) ==
  IF e \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = e
  ELSE 0

(* 5. Last element of a sequence (Null if empty). *)
Last(seq) == IF Len(seq) = 0 THEN Null ELSE seq[Len(seq)]

(* 6. Test if a sequence is empty. *)
IsEmpty(seq) == Len(seq) = 0

(* 7. Remove all occurrences of an element from a sequence. *)
RECURSIVE RemoveAll(_,_)
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = e
       THEN RemoveAll(SubSeq(seq, 2, Len(seq)), e)
       ELSE << seq[1] >> \o RemoveAll(SubSeq(seq, 2, Len(seq)), e)

(* 8. Intersection of a set of sets. *)
SetIntersection(S) == { x \in UNION S : \A A \in S : x \in A }

(* 9. Generate all permutations of a finite set. *)
RECURSIVE SetPermutations(_)
SetPermutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in SetPermutations(S \ {e}) }

(* 10. Test helper that prints diagnostic information on failure. *)
TestHelper(expr, msg) ==
  IF expr THEN TRUE
  ELSE (Print(msg) = msg) /\ FALSE

(***************************************************************************)
(* Trivial specification scaffolding – required identifiers               *)
(***************************************************************************)

VARIABLE dummy

Spec == TRUE

SPECIFICATION == Spec

INIT == TRUE

NEXT == UNCHANGED dummy

====