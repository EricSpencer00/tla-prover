---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxVal

VARIABLES seq

vars == <<seq>>

TypeOK ==
    /\ seq \in Seq(0 .. MaxVal)

Init ==
    /\ seq = << >>

Intersect(s1, s2) ==
    /\ (s1 \cap s2) # {}

SetReduce(f, S, init) ==
    LET g[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE
            LET x == CHOOSE e \in T : TRUE
                rest == T \ {x}
            IN f(x, g[rest])
    IN g[S]

SeqReduce(f, s, init) ==
    Fold(f, s, init)

IndexOf(s, x) ==
    \E i \in 1 .. Len(s) : s[i] = x /\ i

SeqToSet(s) ==
    {s[i] : i \in 1 .. Len(s)}

Last(s) ==
    s[Len(s)]

SequenceEmpty(s) ==
    Len(s) = 0

Remove(s, x) ==
    SelectSeq(s, LAMBDA y : y # x)

IntersectionOf(S) ==
    IF S = {} THEN {}
    ELSE LET f[i \in S] == Cardinality(i) IN {x \in UNION S : \A i \in S : x \in i}

Permutations(S) ==
    [s \in Seq(S) : \A i \in 1 .. Len(s) - 1 : s[i] # s[i + 1]]

Spec ==
    /\ Init
    /\ [][Init]_vars

Specification == Spec

INVARIANTS == TRUE

PROPERTIES == TRUE

====