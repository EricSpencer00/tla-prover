---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Utility library for the key-value store specifications.                *)
(*  Provides a collection of reusable operators for set and sequence       *)
(*  manipulation.  No state variables are introduced here; the module      *)
(*  is purely functional.                                                  *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\*  1) Set intersection test: true iff two sets have a non‑empty overlap.
\* ----------------------------------------------------------------------
SetIntersect(s, t) ==  /\ s \in SUBSET UNIV
                     /\ t \in SUBSET UNIV
                     /\ (s \cap t) # {}

\* ----------------------------------------------------------------------
\*  2) Maximum and minimum element of a non‑empty finite set.
\* ----------------------------------------------------------------------
SetMax(s) == 
    LET f == [x \in s |-> x] IN
    CHOOSE y \in s : \A z \in s : y >= z

SetMin(s) == 
    LET f == [x \in s |-> x] IN
    CHOOSE y \in s : \A z \in s : y <= z

\* ----------------------------------------------------------------------
\*  3) Generalized set reduction (fold) with an accumulator.
\*     Op must be a binary operator that yields a value of the same type
\*     as the accumulator.
\* ----------------------------------------------------------------------
SetReduce(Init, Op, s) ==
    IF s = {} THEN Init
    ELSE LET a == CHOOSE x \in s : TRUE IN
         SetReduce(Op(Init, a), Op, s \ {a})

\* ----------------------------------------------------------------------
\*  4) Sequence reduction (fold) using the library SeqFold.
\* ----------------------------------------------------------------------
SeqReduce(Init, Op, sq) == SeqFold(Op, Init, sq)

\* ----------------------------------------------------------------------
\*  5) Index of an element in a sequence (returns 0 if the element does not
\*     appear).  The returned index is 1‑based, matching the semantics of
\*     the built‑in \A i \in 1..Len(sq) : sq[i] = elt.
\* ----------------------------------------------------------------------
SeqIdx(el, sq) ==
    IF \E i \in 1..Len(sq) : sq[i] = el
    THEN CHOOSE i \in 1..Len(sq) : sq[i] = el
    ELSE 0

\* ----------------------------------------------------------------------
\*  6) Convert a sequence to the set of its elements.
\* ----------------------------------------------------------------------
SeqToSet(sq) == { sq[i] : i \in 1..Len(sq) }

\* ----------------------------------------------------------------------
\*  7) Last element of a non‑empty sequence.
\* ----------------------------------------------------------------------
SeqLast(sq) == sq[Len(sq)]

\* ----------------------------------------------------------------------
\*  8) Test whether a sequence is empty.
\* ----------------------------------------------------------------------
SeqIsEmpty(sq) == Len(sq) = 0

\* ----------------------------------------------------------------------
\*  9) Remove all occurrences of a given element from a sequence.
\* ----------------------------------------------------------------------
SeqRemove(el, sq) ==
    << >> \o [ i \in 1..Len(sq) : IF sq[i] # el THEN sq[i] ELSE @NULL ]

\* ----------------------------------------------------------------------
\* 10) Intersection of a set of sets.
\* ----------------------------------------------------------------------
SetIntersection(ss) ==
    IF ss = {} THEN {}
    ELSE \A s \in ss : s

\* ----------------------------------------------------------------------
\* 11) Generate all permutations of a finite set.
\* ----------------------------------------------------------------------
Permutations(s) ==
    IF s = {} THEN { << >> }
    ELSE { << e >> \o p : e \in s, p \in Permutations(s \ {e}) }

\* ----------------------------------------------------------------------
\* 12) Assertion helper that prints a message on failure.
\* ----------------------------------------------------------------------
Assert(test, msg) == 
    IF test THEN TRUE
    ELSE
        /\ Print(msg)
        /\ FALSE

(***************************************************************************)
(*  SPECIFICATION, INIT, NEXT, INVARIANTS, PROPERTIES                      *)
(*  The reference configuration expects these identifiers to exist, but   *)
(*  the module does not model any state.  Therefore we provide a trivial   *)
(*  specification that does not constrain the system.                      *)
(***************************************************************************)

VARIABLE dummy

SPECIFICATION == Init /\ []Next

Init == dummy = 0

Next == /\ dummy' = dummy

INVARIANTS == TRUE

PROPERTIES == TRUE

====