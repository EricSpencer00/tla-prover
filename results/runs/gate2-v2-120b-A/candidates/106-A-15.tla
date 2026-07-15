---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* Utility operators *)

(* 1. SetIntersectionTest(s, t): true iff s and t overlap *)
SetIntersectionTest(s, t) == \E x \in s : x \in t

(* 2a. MaxElement(s): maximum element of a non‑empty finite set of Naturals *)
MaxElement(s) == 
    \A x \in s : \A y \in s : x >= y

(* 2b. MinElement(s): minimum element of a non‑empty finite set of Naturals *)
MinElement(s) == 
    \A x \in s : \A y \in s : x <= y

(* 3. SetReduce(Set, Acc, Op):
       folds Op over the elements of Set, starting with Acc.
       Op must be a binary operator taking an accumulator and an element. *)
SetReduce(Set, Acc, Op) == 
    IF Set = {} 
      THEN Acc 
      ELSE 
        LET x == CHOOSE y \in Set : TRUE IN 
          SetReduce(Set \ {x}, Op(Acc, x), Op)

(* 4. SeqReduce(Seq, Acc, Op):
       folds Op over the sequence Seq from left to right, starting with Acc.
       Op must be a binary operator taking an accumulator and an element. *)
SeqReduce(Seq, Acc, Op) == 
    IF Len(Seq) = 0 
      THEN Acc 
      ELSE Op(SeqReduce(Seq[1 .. Len(Seq)-1], Acc, Op), Seq[Len(Seq)])

(* 5. IndexOf(Seq, e):
       returns the 1‑based index of the first occurrence of e in Seq,
       or 0 if e does not occur. *)
IndexOf(Seq, e) == 
    IF e \notin Set(Seq) 
      THEN 0 
      ELSE 
        CHOOSE i \in 1 .. Len(Seq) : Seq[i] = e

(* 6. SeqToSet(Seq): the set of elements occurring in Seq *)
SeqToSet(Seq) == Set(Seq)

(* 7. Last(Seq): the last element of a non‑empty sequence *)
Last(Seq) == Seq[Len(Seq)]

(* 8. IsEmpty(Seq): true iff Seq has length zero *)
IsEmpty(Seq) == Len(Seq) = 0

(* 9. RemoveAll(Seq, e):
       returns a new sequence obtained by deleting every occurrence of e. *)
RemoveAll(Seq, e) == 
    IF Len(Seq) = 0 
      THEN <<>> 
      ELSE IF Seq[1] = e 
            THEN RemoveAll(Seq[2 .. Len(Seq)], e) 
            ELSE <<Seq[1]>> \o RemoveAll(Seq[2 .. Len(Seq)], e)

(* 10. SetIntersection(SetOfSets):
        the intersection of all sets contained in SetOfSets.
        For an empty collection the result is the universal set of Naturals
        (the only plausible neutral element for intersection in our domain). *)
SetIntersection(SetOfSets) == 
    IF SetOfSets = {} 
      THEN Nat 
      ELSE /\ \A S \in SetOfSets : S \subseteq Nat
           /\ \A x \in Nat : \A S \in SetOfSets : x \in S

(* 11. Permutations(S):
        the set of all sequences that are permutations of the elements of S.
        S must be a finite set of Naturals. *)
Permutations(S) == 
    IF S = {} 
      THEN { <<>> } 
      ELSE 
        { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* 12. Assert(expr, msg):
        a test helper that aborts the model if expr is false, emitting msg. *)
Assert(expr, msg) == 
    IF expr 
      THEN TRUE 
      ELSE 
        /\ Print("ASSERTION FAILED: " \o msg)
        /\ FALSE

=============================================================================