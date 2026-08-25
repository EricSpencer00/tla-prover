---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Utility operators for set and sequence manipulation                    *)
(***************************************************************************)

\* 1. Set intersection test (whether two sets overlap)
Overlaps(S, T) == ∃ x \in S : x \in T

\* 2. Maximum and minimum element selection from a set (assumes comparable elements)
MaxElem(S) ==
  IF S = {} THEN
    (* No maximum for empty set *) 0
  ELSE
    CHOOSE x \in S : \A y \in S : y <= x

MinElem(S) ==
  IF S = {} THEN
    (* No minimum for empty set *) 0
  ELSE
    CHOOSE x \in S : \A y \in S : y >= x

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, f(_,_), init) ==
  LET seq == SetToSeq(S) IN
    SeqReduce(seq, f, init)

\* Helper: convert a finite set to a sequence (arbitrary order)
SetToSeq(S) ==
  IF S = {} THEN <<>>
  ELSE
    LET
      n == Cardinality(S)
      enum == [i \in 1..n |-> CHOOSE x \in S : 
                \A j \in 1..(i-1) : enum[j] # x]
    IN  [i \in 1..n |-> enum[i]]

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, f(_,_), init) ==
  IF Len(seq) = 0 THEN init
  ELSE SeqReduce(Tail(seq), f, f(init, Head(seq)))

\* 5. Finding the index of an element in a sequence
IndexOf(seq, e) ==
  IF \E i \in 1..Len(seq) : seq[i] = e THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = e
  ELSE -1

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
Last(seq) ==
  IF Len(seq) = 0 THEN
    (* undefined for empty sequence *) 0
  ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE
    IF Head(seq) = e THEN
      RemoveAll(Tail(seq), e)
    ELSE
      << Head(seq) >> \o RemoveAll(Tail(seq), e)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
  { x : \A S \in SS : x \in S }

\* 11. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE
    UNION { { <<e>> \o p : p \in Permutations(S \ {e}) } : e \in S }

\* 12. Test helper for writing assertions that print diagnostic information on failure
TestHelper(cond, msg) ==
  cond \/ (Print(msg) /\ FALSE)

(***************************************************************************)
(* Trivial specification skeleton required by the configuration           *)
(***************************************************************************)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====