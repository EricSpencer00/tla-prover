---- MODULE Util ----
EXTENDS Integers, Sequences

CONSTANTS MaxSequence, MaxKey, MaxIterations

\* Returns whether two sets overlap.
SetIntersection(s1, s2) == \E x \in s1 : x \in s2

\* Returns the maximum element of a non-empty set of integers.
SetMaximum(S) ==
  CHOOSE m \in S : \A x \in S : x <= m

\* Returns the minimum element of a non-empty set of integers.
SetMinimum(S) ==
  CHOOSE m \in S : \A x \in S : m <= x

\* Generalized reduction over a set: fold an operator over its elements
\* in an arbitrary order using an accumulator.
SetReduce(Set, Zero, Op) ==
  LET
    Seen == {x \in Set : x <= Zero}
    Unseen == Set \ Seen
    Total == [x \in Set |-> IF x \in Seen THEN Zero ELSE x]
    Pick(x) == CHOOSE y \in Unseen : TRUE
    Sum(x) == IF x = {} THEN Zero
              ELSE LET y == Pick(x) IN Op(Total[y], Sum(x \ {y}))
  IN Sum(Set)

\* Reduction over a sequence (left fold) using the library Sequences.FoldL.
SequenceReduce(seq, zero, op) ==
  Sequences.FoldL(seq, zero, LAMBDA a, b : op(a, b))

\* Zero-based index of element x in seq, or -1 if absent.
SequenceIndex(seq, x) ==
  LET
    Len == Len(seq)
    Scan(i \in 0..Len) == IF i = Len THEN -1
                         ELSE IF seq[i] = x THEN i
                         ELSE Scan(i + 1)
  IN Scan(0)

\* Returns the set of elements appearing in a sequence.
SequenceToSet(seq) ==
  {seq[i] : i \in DOMAIN seq}

\* Returns the last element of a non-empty sequence.
SequenceLast(seq) == seq[Len(seq) - 1]

\* Returns TRUE iff a sequence has no elements.
SequenceEmpty(seq) == seq = <<>>

\* Returns a copy of seq with all occurrences of x removed.
SequenceRemoveAll(seq, x) ==
  SELECT y \in {z \in [1..MaxSequence -> 0..MaxKey] :
                 \E i \in DOMAIN seq : z[i] = seq[i]}
    : y = [i \in 1..MaxSequence |-> IF \E j \in DOMAIN seq :
                                      /\ seq[j] = seq[i]
                                      /\ j <= i
                                      /\ \A h \in DOMAIN seq :
                                           seq[h] = seq[i] => h <= j
                                      /\ z[i] = seq[j]
                                    THEN seq[j] ELSE 0]

\* Returns the intersection of a set of sets.
SetIntersectionOfSets(sets) ==
  {x \in UNION sets : \A Y \in sets : x \in Y}

\* Returns the set of all permutation sequences of the finite set s.
SetPermutations(s) ==
  LET
    Permutations(ss) ==
      IF ss = {} THEN {<<>>}
      ELSE
        UNION { [x] \o p \in Permutations(ss \ {x}) : x \in ss }
    Pad(seq) ==
      IF Len(seq) < MaxSequence
        THEN seq \o << 0 >>
        ELSE seq
    Trim(seq) ==
      IF seq = <<>> THEN seq
      ELSE IF seq[Len(seq)] = 0
        THEN Trim(seq[1..Len(seq) - 1])
        ELSE seq
  IN {Trim(Pad(p)) : p \in Permutations(s)}

\* Test helper: throws a run-time error with a diagnostic message if its
\* assertion fails, useful for writing invariants and assertions.
TestHelper(b, msg) ==
  IF b THEN TRUE ELSE (Message(msg) /\ FALSE)

====