---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS

\* SPECIFICATION: the operators below are the library's public interface.
\* INIT/NEXT: the module is a pure library, so these are always-enabled stubs.
\* INVARIANTS/PROPERTIES: no safety or liveness properties are defined here.

SPECIFICATION == "Specification"
INIT == "Init"
NEXT == "Next"
INVARIANTS == "Invariants"
PROPERTIES == "Properties"

\* 1. set intersection test: does a and b have a common element?
Overlap(a, b) == \E x \in a : x \in b

\* 2. maximum (or minimum) element selection from a set.
MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

\* 3. generalized set reduction (fold over a set with an accumulator).
FoldSet(f, S, seed) ==
    LET g[T \in SUBSET S] ==
        IF T = {} THEN seed
        ELSE LET x == CHOOSE y \in T : TRUE
             IN f[x, g[T \ {x}]]
    IN g[S]

\* 4. sequence reduction (fold over a sequence with an accumulator).
FoldSeq(f, seq) == FoldSeq(f, seq, 0)
FoldSeq(f, seq, seed) ==
    IF seq = <<>> THEN seed
    ELSE f[Head(seq), FoldSeq(f, Tail(seq), seed)]

\* 5. find the index of an element in a sequence (1-based, or 0 if absent).
IndexOf(seq, x) ==
    LET g[i \in 1..Len(seq)] ==
        IF seq[i] = x THEN i ELSE IF i = Len(seq) THEN 0 ELSE g[i + 1]
    IN g[1]

\* 6. convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. get the last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* 8. test if a sequence is empty.
IsEmpty(seq) == Len(seq) = 0

\* 9. remove all occurrences of an element from a sequence.
Remove(seq, x) ==
    IF seq = <<>> THEN <<>>
    ELSE IF Head(seq) = x THEN Remove(Tail(seq), x)
    ELSE <<Head(seq)>> \o Remove(Tail(seq), x)

\* 10. intersection of a set of sets.
InterSet(T) == { x \in UNION T : \A Y \in T : x \in Y }

\* 11. all permutation sequences of a finite set.
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* 12. test helper: assert a condition, supplying a diagnostic on failure.
Assert(cond, msg) == IF cond THEN TRUE ELSE msg

\* Stub definitions: a library module has no behavior of its own.
Spec == Spec /\ Spec' = Spec
Init == Init /\ TRUE
Next == Next /\ TRUE
TypeOK == TRUE
SpecTypeOK == TRUE
====