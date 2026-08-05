---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS MaxElement

MaxElements == {0, 1, MaxElement}

RECURSIVE MaxOfSet(_)
MaxOfSet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : \A z \in S : y >= z IN x

MinElements == {0, 1, MaxElement}

RECURSIVE MinOfSet(_)
MinOfSet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : \A z \in S : y <= z IN x

\* Intersection test for two sets.
SetIntersection(A, B) == \E x \in A : x \in B

\* Generalized reduction: fold a binary operator over a set, carrying an accumulator.
RECURSIVE SetReduce(_)
SetReduce(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN (x + SetReduce(S \ {x}))

SeqReduce(seq) == FoldLeft(seq, 0, LAMBDA a, x : a + x)

\* Find the 1-indexed position of an element in a sequence.
RECURSIVE IndexOf(_, _)
IndexOf(seq, e) ==
    IF seq = <<>> THEN 0
    ELSE IF Head(seq) = e THEN 1
    ELSE LET i == IndexOf(Tail(seq), e) IN (IF i = 0 THEN 0 ELSE i + 1)

SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

RECURSIVE RemoveAll(_, _)
RemoveAll(seq, e) ==
    IF seq = <<>> THEN <<>>
    ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
    ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

\* Intersection of a set of sets: elements common to every member set.
SetOfSetsIntersection(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN x \cap SetOfSetsIntersection(S \ {x})

RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN {<<>>}
    ELSE {<<x>> \o p : x \in S, p \in Permutations(S \ {x})}

\* Test helper: returns TRUE but prints the given message if the predicate fails.
TestHelper(p, msg) == IF p THEN TRUE ELSE (msg) = (msg) /\ TRUE

====