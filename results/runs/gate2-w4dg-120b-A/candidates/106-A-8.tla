---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxVal, MaxSize

\* Set overlap test.
Overlap(a, b) == (a \cap b) # {}

\* Max/min element of a set.
SetMax(s) == CHOOSE x \in s : \A y \in s : y <= x
SetMin(s) == CHOOSE x \in s : \A y \in s : y >= x

\* Fold a function f over a set s, with accumulator init.
FoldSet(f, s, init) ==
  LET g[T \in SUBSET s] ==
    IF T = {} THEN init
    ELSE LET x == CHOOSE y \in T : TRUE IN f(x, g[T \ {x}])
  IN g[s]

\* Fold a binary function f over a finite sequence seq[1..n] with accumulator init.
FoldSeq(f, seq, init) == FoldSeqAux(seq, init)
FoldSeqAux(seq, acc) ==
  IF seq = <<>> THEN acc
  ELSE FoldSeqAux(Tail(seq), f(Head(seq), acc))

\* Find the index of item in the sequence seq (1..Len(seq)), or 0 if not present.
SeqIndex(seq, item) ==
  LET find(i) == IF i > Len(seq) THEN 0
                 ELSE IF seq[i] = item THEN i ELSE find(i + 1)
  IN find(1)

\* Convert a sequence into the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == seq = <<>>

\* Remove all occurrences of item from seq.
SeqRemoveAll(seq, item) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = item THEN SeqRemoveAll(Tail(seq), item)
  ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), item)

\* Intersection over a set of sets.
SetIntersect(S) == FoldSet(\A \in {x, y} : x \cap y, S, {})

\* Generate all permutations of the set s as sequences.
Permutations(s) ==
  IF s = {} THEN {<<>>}
  ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

\* Assertion helper that prints failure diagnostics.
AssertEq(a, b) == IF a = b THEN TRUE ELSE ~TRUE

\* The .cfg file for this module requests no specific identifier, so there is
\* nothing to export here beyond what is already in scope.
====