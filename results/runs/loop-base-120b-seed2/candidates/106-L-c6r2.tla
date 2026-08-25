---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NULL

VARIABLE dummy

(* ----------------------------------------------------------------------
   Basic state (placeholder, not used by utility operators)
   ---------------------------------------------------------------------- *)

INIT == dummy = 0

NEXT == UNCHANGED dummy

SPECIFICATION == INIT /\ [][NEXT]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

(* ----------------------------------------------------------------------
   Utility operators
   ---------------------------------------------------------------------- *)

(* Set overlap test: true iff the two sets have a non‑empty intersection *)
SetOverlap(S, T) == (S \cap T) # {}

(* Maximum and minimum element of a (finite) set.  Returns NULL for the empty set. *)
SetMax(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S: \A y \in S: y <= x

SetMin(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S: \A y \in S: x <= y

(* ----------------------------------------------------------------------
   Generalized set reduction (fold) with an accumulator.
   ---------------------------------------------------------------------- *)

RECURSIVE SetFold(_,_,_)
SetFold(S, e, f) ==
  IF S = {} THEN e
  ELSE
    LET x == CHOOSE y \in S: TRUE IN
      SetFold(S \ {x}, f(e, x), f)

(* Sequence reduction using the library FoldSeq operator. *)
SeqFold(seq, e, f) == FoldSeq(seq, e, f)

(* Index of an element in a sequence (or -1 if not present). *)
IndexOf(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in DOMAIN seq: seq[i] = elem
  ELSE -1

(* Convert a sequence to the set of its elements. *)
SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

(* Retrieve the last element of a sequence, or NULL if the sequence is empty. *)
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

(* Test whether a sequence is empty. *)
IsEmpty(seq) == Len(seq) = 0

(* ----------------------------------------------------------------------
   Remove all occurrences of an element from a sequence.
   ---------------------------------------------------------------------- *)

RECURSIVE RemoveAll(_, _)
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem THEN RemoveAll(Tail(seq), elem)
  ELSE <<seq[1]>> \o RemoveAll(Tail(seq), elem)

(* ----------------------------------------------------------------------
   Intersection of a set of sets (implemented without \bigcap to avoid
   parsing issues).
   ---------------------------------------------------------------------- *)

SetIntersect(a, b) == a \cap b

SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE
    LET init == CHOOSE s \in SS: TRUE
    IN SetFold(SS \ {init}, init, SetIntersect)

(* ----------------------------------------------------------------------
   Permutations of a finite set (delegates to the standard library operator).
   ---------------------------------------------------------------------- *)

PermutationsOf(S) == Permutations(S)

(* ----------------------------------------------------------------------
   Assertion helper that prints a diagnostic message on failure.
   ---------------------------------------------------------------------- *)

AssertEqual(actual, expected, msg) ==
  IF actual = expected THEN TRUE
  ELSE (Print(msg, " expected=", expected, " actual=", actual) /\ FALSE)

====