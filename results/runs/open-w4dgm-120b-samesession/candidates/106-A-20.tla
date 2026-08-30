---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxElem, MaxLen

VARIABLES TestCounter

Operators == {"Intersection", "MinMax", "SetReduce", "SeqReduce", "FindIndex",
              "ToSet", "LastEl", "IsEmpty", "RemoveAll", "IntersectFamily",
              "Permutations", "TestHelper"}

TypeOK ==
    /\ TestCounter \in 0..2
    /\ \A o \in Operators : TRUE

Init ==
    /\ TestCounter = 0

Intersect(a, b) == Cardinality(a \cap b) > 0

MinMax(s) == [min |-> CHOOSE m \in s : \A x \in s : m <= x,
              max |-> CHOOSE M \in s : \A x \in s : x <= M]

SetReduce(f, s, a) ==
    LET g[T \in SUBSET s] ==
        IF T = {} THEN a
        ELSE LET x == CHOOSE y \in T : TRUE IN f(g[T \ {x}], x)
    IN g[s]

SeqReduce(f, seq, a) == FoldSeq(f, a, seq)

FindIndex(seq, e) ==
    CHOOSE i \in 1..Len(seq) : seq[i] = e

ToSet(seq) == {seq[i] : i \in 1..Len(seq)}

LastEl(seq) == seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

RemoveAll(seq, e) ==
    [i \in 1..(Len(seq) - Cardinality({j \in 1..Len(seq) : seq[j] = e})) |-> CHOOSE k \in 1..Len(seq) :
        /\ seq[k] = e
        /\ \A m \in 1..i : (seq[m] = e => m < k)
        /\ \A m \in 1..(i - 1) : seq[m] # e => seq[m] = seq[m + (IF m + (i - 1) >= k THEN 1 ELSE 0)]
    ]

IntersectFamily(F) ==
    LET elems == UNION {F[i] : i \in DOMAIN F}
    IN {x \in elems : \A i \in DOMAIN F : x \in F[i]}

Permutations(s) ==
    IF s = {} THEN {<<>>}
    ELSE {<<x>> \o p : x \in s, p \in Permutations(s \ {x})}

TestHelper(b) ==
    /\ b
    /\ TestCounter' = (TestCounter + 1) % 3
    /\ \A o \in Operators : o \in Operators

Next == Init \/ TestHelper(TRUE)

Spec ==
    /\ Init
    /\ [][Next]_<<TestCounter>>

SpecOK == Spec

====