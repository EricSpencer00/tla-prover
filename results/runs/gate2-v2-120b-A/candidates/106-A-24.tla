---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Utility library module providing common helper operators for the       *)
(* key‑value store specifications.                                         *)
(***************************************************************************)

\*=======================================================================
\* Set intersection test: Two sets overlap?
\*=======================================================================
SetOverlap(A, B) == A \cap B # {}

\*=======================================================================
\* Maximum element of a finite, non‑empty set.
\*=======================================================================
SetMax(S) == 
  IF S = {} THEN 0 
  ELSE CHOOSE x \in S : \A y \in S : y <= x

\*=======================================================================
\* Minimum element of a finite, non‑empty set.
\*=======================================================================
SetMin(S) == 
  IF S = {} THEN 0 
  ELSE CHOOSE x \in S : \A y \in S : x <= y

\*=======================================================================
\* Generalized set reduction (fold) with an accumulator.
\*   f  – binary operator (accumulator, element) -> new accumulator
\*   A0 – initial accumulator value
\*   S  – finite set to be reduced
\*=======================================================================
SetReduce(f, A0, S) ==
  IF S = {} THEN A0
  ELSE 
    LET x == CHOOSE e \in S : TRUE \* arbitrary element
    IN SetReduce(f, f(A0, x), S \ {x})

\*=======================================================================
\* Sequence reduction (fold) using the library operator FoldSeq.
\*   f  – binary operator (accumulator, element) -> new accumulator
\*   A0 – initial accumulator value
\*   s  – sequence to be reduced
\*=======================================================================
SeqReduce(f, A0, s) == FoldSeq(f, A0, s)

\*=======================================================================
\* Index of the first occurrence of element e in sequence s.
\* Returns 0 if e is not present.
\*=======================================================================
SeqIndex(e, s) ==
  IF e \in SeqToSet(s) THEN
    CHOOSE i \in 1..Len(s) : s[i] = e
  ELSE 0

\*=======================================================================
\* Convert a sequence to the set of its elements.
\*=======================================================================
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\*=======================================================================
\* Return the last element of a non‑empty sequence.
\*=======================================================================
SeqLast(s) == s[Len(s)]

\*=======================================================================
\* Test whether a sequence is empty.
\*=======================================================================
SeqIsEmpty(s) == Len(s) = 0

\*=======================================================================
\* Remove all occurrences of element e from sequence s.
\*=======================================================================
SeqRemoveAll(e, s) ==
  IF Len(s) = 0 THEN s
  ELSE IF s[1] = e THEN SeqRemoveAll(e, Tail(s))
       ELSE << s[1] >> \o SeqRemoveAll(e, Tail(s))

\*=======================================================================
\* Intersection of a set of sets.
\*=======================================================================
SetIntersection(T) ==
  IF T = {} THEN {}
  ELSE \* compute intersection iteratively
       LET S0 == CHOOSE X \in T : TRUE \* arbitrary element of T
       IN SetReduce(\A A, B \in S0 : A \cap B, S0, T \ {S0})

\*=======================================================================
\* Generate all permutations of a finite set.
\* Returns a set of sequences, each a permutation of the elements of S.
\*=======================================================================
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE 
    UNION { 
      << x >> \o p :
        x \in S,
        p \in Permutations(S \ {x})
    }

\*=======================================================================
\* Test helper for assertions that prints diagnostic information on failure.
\* The operator simply returns TRUE when the condition holds; when it does
\* not hold it raises an error that TLC reports.
\*=======================================================================
TEST(cond, msg) ==
  IF cond THEN TRUE
  ELSE 
    (* The following construct forces an assertion failure with a message. *)
    LET _ == 
      Print("\n*** TEST FAILED: ", msg, " ***\n")
    IN FALSE

\*=======================================================================
\* No state variables, actions, or properties are defined in this library.
\*=======================================================================
\* The configuration file may refer to SPECIFICATION, INIT, NEXT, 
\* INVARIANTS, or PROPERTIES, but they are not needed for this module.
\* They are therefore left undefined.

====