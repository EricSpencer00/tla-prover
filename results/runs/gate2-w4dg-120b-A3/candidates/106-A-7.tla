---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS NONE

INTERSECT(a, b) == Cardinality(a \cap b) > 0

MAX(a) == CHOOSE x \in a : \A y \in a : y <= x
MIN(a) == CHOOSE x \in a : \A y \in a : y >= x

SETREDUCE(f, S, z) ==
    LET g[T \in SUBSET S] ==
        IF T = {} THEN z
        ELSE LET x == CHOOSE y \in T : TRUE
             IN f[x, g[T \ {x}]]
    IN g[S]

SEQREDUCE(f, s, z) == Reduce(f, s, z)

INDEX(s, x) == CHOOSE i \in DOMAIN s : s[i] = x

SEQ2SET(s) == {s[i] : i \in DOMAIN s}

LAST(s) == s[Len(s)]

EMPTY(s) == Len(s) = 0

REMOVEALL(s, x) == [i \in 1..Len(s) |-> IF s[i] = x THEN NONE ELSE s[i]]

INTERSECTION(a) ==
    LET r[T \in SUBSET a] ==
        IF T = {} THEN {}
        ELSE LET x == CHOOSE y \in T : TRUE
             IN r[T \ {x}] \cup x
    IN r[a]

PERMUTE(d) ==
    LET f[T \in SUBSET d] ==
        IF T = {} THEN << >>
        ELSE
            LET x == CHOOSE y \in T : TRUE
                rest == f[T \ {x}]
            IN {<<x>>} \o rest
    IN {s \in f[d] :TRUE}

TestHelper(p) == IF p THEN TRUE ELSE (Print("assertion failed"); FALSE)

Spec == TRUE
Init == TRUE
Next == TRUE
Invariants == {}
Properties == {}

====