---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Domain

\* set intersection: true iff two sets have at least one common element
HasIntersection(S1, S2) == \E e \in S1 : e \in S2

\* maximum element of a set (arbitrary but fixed for a given set)
\* (iterates over the set to find the greatest)
Max(S) == LET a \in S == CHOOSE a \in S : \A x \in S : x <= a IN a

\* minimum element of a set
Min(S) == LET a \in S == CHOOSE a \in S : \A x \in S : a <= x IN a

\* reduce a set with an accumulator and a binary function, folding in arbitrary order
SetReduce(S, op, base) ==
    LET R[b \in SUBSET S] ==
        IF b = {} THEN base
        ELSE LET e \in b == CHOOSE e \in b : TRUE
             IN op[e, R[b \ {e}]]
    IN R[S]

\* sequence reduction using the built-in fold operator (left associative)
SeqReduce(seq, op, base) == FoldSeq(seq, base, op)

\* index of an element in a sequence (1-indexed), or 0 if not present
IndexOf(seq, e) == IF \E i \in DOMAIN seq : seq[i] = e
                   THEN CHOOSE i \in DOMAIN seq : seq[i] = e
                   ELSE 0

\* set of elements appearing in a sequence
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* last element of a non-empty sequence
LastOf(seq) == seq[Len(seq)]

NonEmpty(seq) == Len(seq) > 0

\* remove all occurrences of an element from a sequence
RemoveAll(seq, e) ==
    [ i \in 1..(Len(seq) - Cardinality({j \in DOMAIN seq : seq[j] = e}))
      |-> CHOOSE k \in {j \in DOMAIN seq : seq[j] # e} :
            (Cardinality({m \in DOMAIN seq : seq[m] # e /\ m < k}) = i - 1) ]

\* intersection of a set of sets
SetIntersection(F) == SetReduce(F, (x,y) |-> x \cap y, Domain)

\* all permutations of a set (as sequences)
AllPermutations(S) ==
    LET Perm[T \in SUBSET S] ==
        IF T = {} THEN { << >> }
        ELSE UNION { [ << e >> \o p \in Perm[T \ {e}] ] : e \in T }
    IN Perm[S]

\* test helper: prints its name and a counterexample when its condition fails
Assert(name, cond) == IF cond THEN TRUE ELSE (Print("FAILED:", name); FALSE)
====