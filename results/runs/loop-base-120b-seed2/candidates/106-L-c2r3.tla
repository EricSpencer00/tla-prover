---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

(* Set overlap test: true iff S and T have a non‑empty intersection *)
SetOverlap(S, T) == (S \cap T) /= {}

(* Maximum element of a non‑empty finite set (assumes a total order) *)
SetMax(S) == 
  CHOOSE x \in S : (\A y \in S : y <= x)

(* Minimum element of a non‑empty finite set (assumes a total order) *)
SetMin(S) == 
  CHOOSE x \in S : (\A y \in S : x <= y)

(* Generalized reduction (fold) over a set, using a binary operator f
   and an initial accumulator init. Order is arbitrary (via Seq) *)
SetReduce(S, init, f) == SeqReduce(Seq(S), init, f)

(* Reduction over a sequence, using a binary operator f and an initial value init *)
RECURSIVE SeqReduce(_,_,_)
SeqReduce(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE f[Head(seq), SeqReduce(Tail(seq), init, f)]

(* Index of the first occurrence of elem in seq (1‑based); 0 if not present *)
IndexOf(seq, elem) ==
  IF elem \in seq THEN
    CHOOSE i \in 1 .. Len(seq) : seq[i] = elem
  ELSE 0

(* Convert a sequence to the set of its elements *)
SeqToSet(seq) == { seq[i] : i \in 1 .. Len(seq) }

(* Last element of a non‑empty sequence *)
Last(seq) == seq[Len(seq)]

(* Test whether a sequence is empty *)
IsEmpty(seq) == Len(seq) = 0

(* Remove all occurrences of elem from seq *)
RECURSIVE RemoveAll(_,_)
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem
       THEN RemoveAll(Tail(seq), elem)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

(* Intersection of a set of sets (may be empty) *)
SetIntersectionOfSets(S) == 
  IF S = {} THEN {} ELSE INTERSECTION(S)

(* Generate all permutations of a finite set S as a set of sequences *)
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

(* Assertion helper that prints a message on failure; returns TRUE iff cond holds *)
AssertHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE (Print(msg); FALSE)

\* ----------------------------------------------------------------------
\* Trivial specification (required identifiers)
\* ----------------------------------------------------------------------

VARIABLE dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_<<dummy>>

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == TRUE
PROPERTIES == TRUE

====