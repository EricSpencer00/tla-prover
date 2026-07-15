---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Utility library operators for the kvstore project.                     *)
(*  The module is intentionally pure and contains no state variables.     *)
(*  It only defines reusable operators, each documented below.            *)
(***************************************************************************)

(********************)
(*  Operators       *)
(********************)

(* 1. Set intersection test: returns TRUE iff the two sets overlap. *)
SetOverlap(A, B) == 
  \E x \in A : x \in B

(* 2. Maximum element of a non‑empty set of naturals. *)
SetMax(S) == 
  IF S = {} THEN -1
  ELSE CHOOSE x \in S : \A y \in S : y <= x

(* 2. Minimum element of a non‑empty set of naturals. *)
SetMin(S) == 
  IF S = {} THEN -1
  ELSE CHOOSE x \in S : \A y \in S : x <= y

(* 3. Generalized set reduction (fold) with a binary operator 'op'.        *)
(*    The operator must be a function of two arguments: accumulator and   *)
(*    element, returning a new accumulator.                               *)
SetReduce(S, acc, op) ==
  IF S = {} THEN acc
  ELSE 
    LET x == CHOOSE e \in S : TRUE IN
      SetReduce(S \ {x}, op(acc, x), op)

(* 4. Sequence reduction (fold) using the binary operator 'op'.          *)
SeqReduce(seq, acc, op) ==
  IF Len(seq) = 0 THEN acc
  ELSE
    LET newAcc == op(acc, seq[1]) IN
      SeqReduce(SubSeq(seq, 2, Len(seq)), newAcc, op)

(* 5. Find the (1‑based) index of element e in sequence seq; returns 0   *)
(*    if e does not occur.                                                *)
SeqIndex(seq, e) ==
  IF e \notin seq THEN 0
  ELSE 1 + SeqIndex(SubSeq(seq, 2, Len(seq)), e)

(* 6. Convert a sequence to the set of its elements.                     *)
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

(* 7. Return the last element of a non‑empty sequence.                    *)
SeqLast(seq) == 
  IF Len(seq) = 0 THEN -1
  ELSE seq[Len(seq)]

(* 8. Test whether a sequence is empty.                                   *)
SeqEmpty(seq) == Len(seq) = 0

(* 9. Remove all occurrences of element e from sequence seq.             *)
SeqRemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = e THEN SeqRemoveAll(SubSeq(seq, 2, Len(seq)), e)
       ELSE <<seq[1]>> \o SeqRemoveAll(SubSeq(seq, 2, Len(seq)), e)

(* 10. Intersection of a set of sets.                                     *)
SetOfSetsIntersection(S) ==
  IF S = {} THEN {}
  ELSE 
    LET first == CHOOSE X \in S : TRUE IN
      \A X \in S : first \subseteq X /\ first = X
      /\ { y \in first : \A X \in S : y \in X }

(* 11. Generate all permutations of the finite set S as a set of sequences. *)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE
    { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

(* 12. Test helper that prints a message on failure.                     *)
TestAssert(cond, msg) ==
  IF cond THEN TRUE
  ELSE
    BEGIN
      Print(msg);
      FALSE
    END

(********************)
(*  Required names  *)
(********************)

(* The specification does not define any state. We expose the required
   identifiers as no‑ops or trivial definitions so the .cfg can refer to
   them without causing undefined‑identifier errors. *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == FALSE
PROPERTIES == FALSE

=============================================================================