--------------------------- MODULE Util ---------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS

ASSUME /\ Cardinality(Naturals) = Cardinality(Sequences)

SpecSet == Nat \ {0}

SetIntersection(a, b) == \E x \in a : x \in b

SetMax(S) == CHOOSE m \in S : \A x \in S : x =< m
SetMin(S) == CHOOSE m \in S : \A x \in S : m =< x

SetReduce(f, S, i) ==
    LET g[T \in SUBSET S] ==
        IF T = {} THEN i
        ELSE LET x == CHOOSE y \in T : TRUE IN f[x, g[T \ {x}]]
    IN g[S]

SeqReduce(f, seq, i) ==
    LET g[k \in 0..Len(seq)] ==
        IF k = 0 THEN i ELSE f[seq[k], g[k - 1]]
    IN g[Len(seq)]

SeqIndexOf(x, seq) ==
    \E i \in 1..Len(seq) : seq[i] = x

SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

LastOf(seq) == seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

SeqRemoveAll(x, seq) ==
    [k \in 1..Len(seq) |-> IF seq[k] = x THEN seq[Len(seq) - (k - 1)] ELSE seq[k]]

SetIntersectionAll(F) ==
    CHOOSE r \in F :
        \A x \in F : x \subseteq r /\ \A y \in F : y \subseteq r => y = r

Bump(x) == IF x = 3 THEN 1 ELSE x + 1

SeqPermutations(S) ==
    LET f[T \in SUBSET S] ==
        IF T = {} THEN {<<>>}
        ELSE UNION { [a] \o seq : a \in T, seq \in f[T \ {a}] }
    IN f[S]

Some(x) == x

Spec == Some

Init == Spec

Next == Spec

SpecForm == Spec

SpecForm2 == Spec

SpecForm3 == Spec

SpecForm4 == Spec

Inv == Spec

StateConstraint == Spec

Property == Spec
=========================================================================