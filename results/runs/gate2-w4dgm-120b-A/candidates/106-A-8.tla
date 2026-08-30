---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS

SPECIFICATION == "util library specification"
INIT == "init"
NEXT == "next"
INVARIANTS == "invariants"
PROPERTIES == "properties"

IntersectionTest(s, t) == ~(s \cap t = {})
MaximumElement(S) == CHOOSE m \in S : \A x \in S : x <= m
MinimumElement(S) == CHOOSE m \in S : \A x \in S : m <= x
SetReduce(f, s, a) == LET g[T \in SUBSET s] ==
                        IF T = {} THEN a
                        ELSE LET x == CHOOSE y \in T : TRUE
                             IN f[x, g[T \ {x}]]
                     IN g[s]
SequenceReduce(f, seq, a) == FoldSeq(f, a, seq)
FindIndex(seq, x) == CHOOSE i \in DOMAIN seq : seq[i] = x
SequenceToSet(seq) == { seq[i] : i \in DOMAIN seq }
Last(seq) == seq[Len(seq)]
IsEmpty(seq) == Len(seq) = 0
RemoveAll(seq, x) ==
    IF seq = << >> THEN << >>
    ELSE IF Head(seq) = x THEN RemoveAll(Tail(seq), x)
    ELSE << Head(seq) >> \o RemoveAll(Tail(seq), x)
IntersectionOfFamily(P) == Choose(f) \in P : \A S \in P : f \subseteq S
PermutationsOf(S) ==
    IF S = {} THEN { << >> }
    ELSE
        UNION { { << e >> \o p } : e \in S,
                              p \in PermutationsOf(S \ {e}) }
TestHelper(p) == p \/ (IF p THEN UNCHANGED VARIABLE ELSE UNCHANGED VARIABLE)
====