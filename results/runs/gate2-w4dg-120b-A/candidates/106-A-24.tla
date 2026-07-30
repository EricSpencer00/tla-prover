---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS MaxElements, MaxValue, MaxSeqLen

\* set intersection test: true iff s1 and s2 share at least one element
Overlaps(s1, s2) == \E x \in s1 : x \in s2

\* maximum element of a non-empty finite set (returns 0 for the empty set)
MaxElement(s) == IF s = {} THEN 0 ELSE CHOOSE x \in s : \A y \in s : y <= x

\* minimum element of a non-empty finite set (returns 0 for the empty set)
MinElement(s) == IF s = {} THEN 0 ELSE CHOOSE x \in s : \A y \in s : y >= x

\* generalized reduction (fold) over a set with an accumulator
SetReduce(f, s, init) ==
  LET g[T \in SUBSET s] ==
        IF T = {} THEN init
        ELSE \E x \in T : \E r \in g[T \ {x}] : f(x, r)
  IN g[s]

\* reduction over a sequence, delegating to the library 'FoldSeq' operator
SeqReduce(f, seq, init) == FoldSeq(seq, init, f)

\* index of element x in sequence seq; -1 means not present
IndexOf(x, seq) ==
  LET g[i \in 0..Len(seq)] ==
        IF i = Len(seq) THEN -1
        ELSE IF seq[i + 1] = x THEN i + 1
        ELSE g[i + 1]
  IN g[0]

\* convert a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* the last element of a sequence, or 0 if the sequence is empty
Last(seq) == IF seq = <<>> THEN 0 ELSE seq[Len(seq)]

\* true iff the sequence is empty
SeqEmpty(seq) == seq = <<>>

\* remove all occurrences of x from a sequence
RemoveAll(seq, x) ==
  \E seq1 \in Seq({}), seq2 \in Seq({}) : seq = seq1 \o seq2 /\ \A y \in seq2 : y # x

\* intersection of a set of sets
SetIntersect(ss) ==
  IF ss = {} THEN {}
  ELSE \E x \in ss : \A y \in ss : x \cap y

\* generate all permutation sequences of a finite set
Permutations(s) ==
  IF s = {} THEN {<<>>}
  ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

\* test helper that returns TRUE but prints an alias, a message, and a value when
\* the condition is FALSE; useful for debugging assertions
TestHelper(alias, msg, cond, val) ==
  IF cond THEN TRUE ELSE (Print(alias), Print(msg), Print(val), TRUE)
====