---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

ASSUME TLC.IsFiniteSet(Natural)

\* Set intersection test: whether two sets overlap (are non-disjoint).
Overlaps(a, b) == \E x \in a : x \in b

\* Maximum element of a finite set of naturals (0 for the empty set, to stay total).
MaxNat(s) == IF s = {} THEN 0 ELSE LET m == CHOOSE x \in s : \A y \in s : y <= x IN m

\* Minimum element of a finite set of naturals (0 for the empty set, to stay total).
MinNat(s) == IF s = {} THEN 0 ELSE LET m == CHOOSE x \in s : \A y \in s : x <= y IN m

\* Generalized reduction over a set: applies operator g to every element, accumulating into o.
ReduceSet(g) == LAMBDA a, o \in Nat, s \in SUBSET Nat :
    LET step(p) == LET a' == p[1] IN LET o' == p[2] IN LET x == p[3] IN g(a', o', x) IN
    LET seq == <<x \in s : step([a, o, x])>> IN
    IF s = {} THEN o ELSE Head(seq)

\* Reduction over a sequence using the library's FoldSeq (doesn't force a fixed shape).
ReduceSeq(g) == LAMBDA a, o \in Nat, s \in Seq(Nat) : FoldSeq(LAMBDA x == g(a, o, x), s)

\* Finds the index of an element in a sequence (0 if not present).
FindIndex(s, x) == LET pos(i) == IF s[i] = x THEN i ELSE 0 IN
    LET seq == <<i \in DOMAIN s : pos(i)>> IN IF seq = <<>> THEN 0 ELSE Head(seq)

\* Converts a sequence to the set of its elements (drops order and duplicates).
SeqToSet(s) == {s[i] : i \in DOMAIN s}

\* Returns the last element of a non-empty sequence; 0 on the empty sequence.
SeqLast(s) == IF s = <<>> THEN 0 ELSE s[Len(s)]

\* Tests whether a sequence is empty.
SeqIsEmpty(s) == s = <<>>

\* Removes all occurrences of a value from a sequence, preserving order.
SeqRemoveAll(s, x) == SelectSeq(s, LAMBDA y == y # x)

\* Intersection of a set of sets; returns the empty set when the collection is empty.
IntersectionOfSets(S) == IF S = {} THEN {} ELSE LET f == CHOOSE s \in S : TRUE IN \A r \in S : f \cap r

\* Generates all permutations of a finite set as a set of sequences.
Permutations(S) == IF S = {} THEN {<<>>} ELSE
    UNION { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* Test helper: asserts a condition, printing a custom message on failure.
Assert(msg, expr) == IF expr THEN TRUE ELSE (Print(msg); FALSE)
====