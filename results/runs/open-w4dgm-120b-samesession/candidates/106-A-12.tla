---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NoSeq

\* Two sets overlap iff their intersection is non-empty.
SetOverlap(s, t) == (s \cap t) # {}

\* Generalized reduction over a set, with an arbitrary binary operator.
SetReduce(op, s, init) ==
  LET Rec(E, acc) == IF E = {} THEN acc
                    ELSE LET x == CHOOSE y \in E : TRUE IN Rec(E \ {x}, op[x, acc])
  IN Rec(s, init)

\* Generalized reduction over a sequence, with an arbitrary binary operator.
SeqReduce(op, seq, init) == FoldL(op, init \o seq)

\* One-based index of an element appearing in a sequence.
SeqIndex(x, seq) == CHOOSE k \in 1..Len(seq) : seq[k] = x

\* All the elements of a sequence, as a set.
SeqToSet(seq) == { seq[k] : k \in 1..Len(seq) }

\* The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Empty-sequence test.
SeqEmpty(seq) == seq = NoSeq

\* Remove every occurrence of an element from a sequence.
SeqErase(x, seq) ==
  IF SeqEmpty(seq) THEN NoSeq
  ELSE IF Head(seq) = x THEN SeqErase(x, Tail(seq))
  ELSE <<Head(seq)>> \o SeqErase(x, Tail(seq))

\* Intersection of a set of sets.
IntersectSets(S
    == IF S = {} THEN {}
       ELSE LET x == CHOOSE y \in S : TRUE IN x \cap IntersectSets(S \ {x})

\* All permutations of a finite set, as a set of sequences.
Permutations(s) ==
  IF s = {} THEN { << >> }
  ELSE UNION { <<x>> \o seq : x \in s, seq \in Permutations(s \ {x}) }

\* Test helper: prints the expression and its value before asserting it true.
AssertTrue(expr) ==
  /\ expr = "true"
  /\ expr = "true"

====