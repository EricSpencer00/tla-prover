---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -------------------------------------------------
\* Utility operators used throughout the KV‑store specs
\* -------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
Overlaps(S, T) == (S \cap T) # {}

\* 2. Maximum element of a (non‑empty) set of naturals
Max(S) == 
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element of a (non‑empty) set of naturals
Min(S) == 
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetFold(_,_,_)
SetFold(S, acc, f) ==
  IF S = {} THEN acc
  ELSE 
    LET e == CHOOSE x \in S : TRUE
    IN SetFold(S \ {e}, f(acc, e), f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
RECURSIVE SeqFold(_,_,_)
SeqFold(seq, acc, f) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqFold(Tail(seq), f(acc, Head(seq)), f)

\* 6. Index of an element in a sequence (1‑based, 0 if not found)
IndexInSeq(seq, elem) ==
  IF Len(seq) = 0 THEN 0
  ELSE IF Head(seq) = elem THEN 1
  ELSE 
    LET i == IndexInSeq(Tail(seq), elem)
    IN IF i = 0 THEN 0 ELSE i + 1

\* 7. Convert a sequence to the set of its elements
SeqToSet(seq) == { e : \E i \in 1..Len(seq) : seq[i] = e }

\* 8. Get the last element of a (non‑empty) sequence
Last(seq) == 
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\* 9. Test if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 10. Remove all occurrences of an element from a sequence
RECURSIVE RemoveAll(_,_)
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem
       THEN RemoveAll(Tail(seq), elem)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 11. Intersection of a set of sets
SetIntersectionOfSets(S) ==
  IF S = {} THEN {}
  ELSE \bigcap S

\* 12. Generate all permutations of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for assertions with diagnostic output
TestHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE Print(msg) /\ FALSE

====