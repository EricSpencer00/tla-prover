---- MODULE Util ----
EXTENDS FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Overlap: test whether two sets have at least one element in common
\* ----------------------------------------------------------------------
Overlap(S1, S2) == (S1 \cap S2) # {}

\* ----------------------------------------------------------------------
\* MaxSet / MinSet: return the maximum / minimum element of a non‑empty set
\* If the set is empty, return NULL
\* ----------------------------------------------------------------------
MaxSet(S) == IF S = {} THEN NULL ELSE MAX S
MinSet(S) == IF S = {} THEN NULL ELSE MIN S

\* ----------------------------------------------------------------------
\* SetFold: generalized fold (reduce) over a set with an accumulator
\* ----------------------------------------------------------------------
SetFold(op, init, S) ==
  IF S = {} THEN init
  ELSE
    LET e   == CHOOSE v \in S : v
        rest == S \ {e}
    IN SetFold(op, op[e, init], rest)

\* ----------------------------------------------------------------------
\* Sequence helpers
\* ----------------------------------------------------------------------
SeqHead(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[1]
SeqTail(seq) == IF Len(seq) < 2 THEN <<>> ELSE SUBSEQ(seq, 2, Len(seq))

\* ----------------------------------------------------------------------
\* SeqFold: generalized fold over a sequence with an accumulator
\* ----------------------------------------------------------------------
SeqFold(op, init, seq) ==
  IF Len(seq) = 0 THEN init
  ELSE
    LET head == SeqHead(seq)
        tail == SeqTail(seq)
    IN SeqFold(op, op[head, init], tail)

\* ----------------------------------------------------------------------
\* SeqIndex: return the 1‑based index of an element in a sequence, or –1 if not found
\* ----------------------------------------------------------------------
SeqIndex(elem, seq) ==
  IF Len(seq) = 0 THEN -1
  ELSE
    LET head == seq[1]
        tail == SUBSEQ(seq, 2, Len(seq))
    IN IF head = elem THEN 1
       ELSE
         LET restIndex == SeqIndex(elem, tail) IN
           IF restIndex = -1 THEN -1 ELSE restIndex + 1

\* ----------------------------------------------------------------------
\* SeqToSet: convert a sequence to the set of its elements
\* ----------------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* ----------------------------------------------------------------------
\* SeqLast: get the last element of a sequence (NULL if the sequence is empty)
\* ----------------------------------------------------------------------
SeqLast(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* ----------------------------------------------------------------------
\* SeqIsEmpty: test whether a sequence is empty
\* ----------------------------------------------------------------------
SeqIsEmpty(seq) == Len(seq) = 0

\* ----------------------------------------------------------------------
\* SeqRemoveAll: remove all occurrences of an element from a sequence
\* ----------------------------------------------------------------------
SeqRemoveAll(elem, seq) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE
    LET head == seq[1]
        tail == SUBSEQ(seq, 2, Len(seq))
    IN IF head = elem THEN SeqRemoveAll(elem, tail)
       ELSE head \o SeqRemoveAll(elem, tail)

\* ----------------------------------------------------------------------
\* SetSetIntersection: intersection of a set of sets (empty set if argument is empty)
\* ----------------------------------------------------------------------
SetSetIntersection(Sets) ==
  IF Sets = {} THEN {}
  ELSE \E x \in \Union(Sets) : \A s \in Sets : x \in s

\* ----------------------------------------------------------------------
\* Permutations: generate all permutation sequences of a finite set
\* ----------------------------------------------------------------------
Permutations(S) ==
  IF S = {} THEN {{<<>>}}
  ELSE
    \E e \in S :
      \E perm \in Permutations[S \ {e}] :
        <<e>> \o perm

\* ----------------------------------------------------------------------
\* Assert helper: returns the condition; the second argument is ignored by the
\* specification but can be used as a diagnostic message in a .cfg file.
\* ----------------------------------------------------------------------
Assert(cond, msg) == cond

====