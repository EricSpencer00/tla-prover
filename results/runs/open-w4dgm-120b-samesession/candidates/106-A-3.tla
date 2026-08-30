---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS IntegerSet

\* Helper that folds a binary operator over a set, starting from an initial value.
SetFold(op, S, init) == LET rf == [a \in [S -> IntegerSet] |-> op[a[1], a[2]]] IN
                          IF S = {} THEN init ELSE rf[CHOOSE f \in [S -> IntegerSet] : TRUE]

\* Helper that folds a binary operator over a sequence, starting from an initial value.
SeqFold(op, seq, init) == LET g[i \in 0..Len(seq)] == IF i = 0 THEN init ELSE op[g[i-1], seq[i]] IN g[Len(seq)]

\* Returns the index of the first occurrence of x in seq, or 0 if x is absent.
SeqIndexOf(x, seq) == IF \E i \in 1..Len(seq) : seq[i] = x THEN CHOOSE i \in 1..Len(seq) : seq[i] = x ELSE 0

\* Membership test for intersection: returns TRUE iff S and T share an element.
SetIntersect(S, T) == Cardinality(S \cap T) > 0

\* Returns the largest element in a non-empty set of integers.
SetMax(S) == SeqFold(LAMBDA a, b : IF a > b THEN a ELSE b, CHOOSE seq \in [1..Cardinality(S) -> IntegerSet] : SetPermutations(S)[seq], CHOOSE e \in S : e)

\* Returns the smallest element in a non-empty set of integers.
SetMin(S) == SeqFold(LAMBDA a, b : IF a < b THEN a ELSE b, CHOOSE seq \in [1..Cardinality(S) -> IntegerSet] : SetPermutations(S)[seq], CHOOSE e \in S : e)

\* Converts a sequence to the set of its elements (filters out the placeholder 0).
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)} \ {0}

\* Returns the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Removes all occurrences of x from seq.
SeqRemoveAll(seq, x) == SELECT seq' \in SetPermutations(seq) : {seq'[i] : i \in 1..Len(seq')} = {seq[i] : i \in 1..Len(seq)} \ {x}

\* Returns the set of elements common to every set in the family.
FamilyIntersection(fam) == {x \in UNION fam : \A S \in fam : x \in S}

\* Returns the set of all permutations of the finite set S.
SetPermutations(S) == { seq \in [1..Cardinality(S) -> IntegerSet] :
    {seq[i] : i \in 1..Cardinality(S)} = S }

\* Prints a diagnostic message and returns FALSE; used to flag failed assertions.
TestHelper == Print("TestHelper triggered").

Spec == TRUE
====