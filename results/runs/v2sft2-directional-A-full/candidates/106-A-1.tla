---- MODULE Util ----
EXTENDS Sequences, FiniteSets, Math, TLC

(* 1. Set intersection test (whether two sets overlap) *)
SetsOverlap(s, t) == (#(s \cap t) > 0)

(* 2. Maximum element selection from a set of natural numbers *)
SetMax(s) == IF s = {} THEN UNDEF ELSE MAX(s)

(* 3. Minimum element selection from a set of natural numbers *)
SetMin(s) == IF s = {} THEN UNDEF ELSE MIN(s)

(* 4. Generalized set reduction (fold over a set with an accumulator) *)
SetReduce(f, acc, s) == SeqReduce(f, acc, Sort(SeqToSet(s)))

(* 5. Sequence reduction (fold over a sequence with an accumulator) *)
SeqReduce(f, acc, seq) == Fold(f, acc, seq)

(* 6. Finding the index of an element in a sequence (1‑based, 0 if not found) *)
SeqIndex(seq, elem) ==
  IF seq = <<>> THEN 0
  ELSE IF Head(seq) = elem THEN 1
  ELSE 1 + SeqIndex(Tail(seq), elem)

(* 7. Converting a sequence to the set of its elements *)
SeqToSet(seq) == SetOf(seq)

(* 8. Getting the last element of a sequence *)
SeqLast(seq) ==
  IF seq = <<>> THEN UNDEF
  ELSE seq[Len(seq)]

(* 9. Testing if a sequence is empty *)
SeqEmpty(seq) == seq = <<>>

(* 10. Removing all occurrences of an element from a sequence *)
SeqRemoveAll(seq, elem) == Filter(seq, e |-> e # elem)

(* 11. Computing the intersection of a set of sets *)
SetIntersectionSetOfSets(sets) ==
  IF sets = {} THEN {}
  ELSE Inter(sets)

(* 12. Generating all permutation sequences of a finite set *)
SetPermutations(set) ==
  IF set = {} THEN {{}} 
  ELSE Permutations(Sort(SeqToSet(set)))

(* 13. Test helper for writing assertions that print diagnostic information on failure *)
TestHelper(msg, actual, expected) ==
  [ok: actual = expected, msg: msg, actual: actual, expected: expected]

====