---- MODULE Util ----
EXTENDS Sequences, FiniteSets

CONSTANTS MaxSeqLen

\* Returns TRUE iff the two sets have a non-empty intersection.
SetOverlap(a, b) == \E x \in a : x \in b

\* Returns the maximum (or minimum) element of a non-empty set, folded with
\* the provided binary operator; works for any totally ordered element type.
SetFold(f, op, init) == LET g[T \in SUBSET a] ==
                          IF T = {} THEN init
                          ELSE \E x \in T : f[x] \oplus g[T \ {x}]
                       IN g[a]

SetMax(a) == SetFold(LAMBDA x : x, ">", 0)
SetMin(a) == SetFold(LAMBDA x : x, "<", MaxSeqLen + 1)

\* Reduces a set with a generic binary operator (a fold over an unordered set).
SetReduce(op, init, s) == LET g[T \in SUBSET s] ==
                            IF T = {} THEN init
                            ELSE \E x \in T : op[x] \oplus g[T \ {x}]
                         IN g[s]

\* Reduces a sequence from the left using the built-in AppendFold operator.
SeqReduce(op, init, seq) == AppendFold(op, init, seq)

SeqIndex(seq, x) ==
  CHOOSE k \in 1..Len(seq) : seq[k] = x
    (* Unique choice: whether the element is present at all is decided
       by the domain restriction, which keeps the index well-defined. *)

SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Returns the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

\* Removes every occurrence of element e from the sequence.
SeqRemove(seq, e) ==
  IF SeqEmpty(seq) THEN seq
  ELSE IF Head(seq) = e THEN SeqRemove(Tail(seq), e)
  ELSE <<Head(seq)>> \o SeqRemove(Tail(seq), e)

\* Intersection of a set of sets: the elements common to all members.
SetIntersection(sets) ==
  {x \in UNION sets : \A s \in sets : x \in s}

\* Generates all permutation sequences of a given finite set.
PermutationsOf(s) ==
  {p \in [1..Cardinality(s) -> UNION s] :
      {p[k] : k \in 1..Cardinality(s)} = s
        /\ \A i, j \in 1..Cardinality(s) : p[i] = p[j] => i = j}

\* Test helper: always TRUE, but prints whatever the caller supplies.
TestHelper(v) == TRUE

====