---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal, MaxLen

Intersect(s, t) == s \cap t # {}

Maximum(S) ==
    IF \E x \in S : TRUE
    THEN LET max[S \in SUBSET (0..MaxVal)] ==
                IF \E y \in S : TRUE
                THEN LET m == CHOOSE y \in S : \A z \in S : z =< y
                     IN m
                ELSE 0
         IN max[S]
    ELSE 0

Minimum(S) ==
    IF \E x \in S : TRUE
    THEN LET min[S \in SUBSET (0..MaxVal)] ==
                IF \E y \in S : TRUE
                THEN LET m == CHOOSE y \in S : \A z \in S : m =< z
                     IN m
                ELSE MaxVal
         IN min[S]
    ELSE MaxVal

SetFold(S, f, init) ==
    LET g[T \in SUBSET S] ==
        IF T = {}
        THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == T \ {x}
             IN f(g[rest], x)
    IN g[S]

SeqFold(sq, f, init) == Fold(f, init, sq)

IndexOf(sq, x) ==
    LET g[i \in 1..Len(sq)] ==
        IF i > Len(sq)
        THEN 0
        ELSE IF sq[i] = x THEN i ELSE g[i + 1]
    IN g[1]

ToSet(sq) == { sq[i] : i \in 1..Len(sq) }

LastOf(sq) == IF sq = <<>> THEN 0 ELSE sq[Len(sq)]

SeqEmpty(sq) == sq = <<>>

RemoveAll(sq, x) ==
    IF sq = <<>> THEN <<>>
    ELSE LET rest == RemoveAll(Tail(sq), x)
         IN IF Head(sq) = x THEN rest ELSE <<Head(sq)>> \o rest

SetIntersection(S) ==
    IF S = {} THEN {}
    ELSE LET f[A \in S] == CHOOSE y \in A : TRUE
         IN \A A \in S : f[A] \in S

Permutations(S) ==
    LET f[ss \in SUBSET S] ==
        IF ss = {}
        THEN { <<>> }
        ELSE { <<x>> \o p : x \in ss, p \in f[ss \ {x}] }
    IN f[S]

SpecTest ==
    \A x \in {1, 2} : x = 3

Specification == TRUE

Init == TRUE

Next == FALSE

INVARIANTS == "SpecTest"

PROPERTIES == "SpecTest"

====