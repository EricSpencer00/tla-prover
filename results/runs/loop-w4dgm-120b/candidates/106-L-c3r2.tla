---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NoElem

VARIABLES specStage

vars == <<specStage>>

SpecStages == {"idle", "running"}

TypeOK ==
    /\ specStage \in SpecStages

Init ==
    /\ specStage = "idle"

StartSpec ==
    /\ specStage = "idle"
    /\ specStage' = "running"

FinishSpec ==
    /\ specStage = "running"
    /\ specStage' = "idle"

Next ==
    \/ StartSpec
    \/ FinishSpec

Spec == Init /\ [Spec EXCEPT !.specStage = "idle"]

\* 1. Set intersection test (do two sets overlap?).
SetIntersects(S, T) == \E x \in S : x \in T

\* 2. Maximum (and minimum) element selection from a set.
SetMax(S) == CHOOSE m \in { y \in S : \A x \in S : y >= x }
SetMin(S) == CHOOSE m \in { y \in S : \A x \in S : y <= x }

\* 3. Generalized set reduction: fold an accumulator over a set.
SetReduce(f, S, a) == IF S = {} THEN a
                      ELSE LET x == CHOOSE y \in S : TRUE
                           IN SetReduce(f, S \ {x}, f[x, a])

\* 4. Sequence reduction (fold) over a sequence with an accumulator.
SeqReduce(f, seq, a) == IF seq = <<>> THEN a
                        ELSE f[Head(seq), SeqReduce(f, Tail(seq), a)]

\* 5. Find the index of an element in a sequence (1-based; 0 = not found).
SeqIndex(seq, e) ==
    LET Scan(i) == IF i > Len(seq) THEN 0
                    ELSE IF seq[i] = e THEN i ELSE Scan(i + 1)
    IN Scan(1)

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) ==
    { seq[i] : i \in 1..Len(seq) }

\* 7. Last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* 8. Test if a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* 9. Remove all occurrences of an element from a sequence.
SeqRemoveAll(seq, e) ==
    IF seq = <<>> THEN <<>>
    ELSE IF Head(seq) = e THEN SeqRemoveAll(Tail(seq), e)
    ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), e)

\* 10. Intersection of a set of sets.
SetFamilyIntersect(FF) ==
    IF FF = {} THEN {}
    ELSE LET x == CHOOSE y \in FF : TRUE
         IN x \cap SetFamilyIntersect(FF \ {x})

\* 11. All permutation sequences of a finite set.
Permutations(S) ==
    IF S = {} THEN {<<>>}
    ELSE { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* 12. Test helper that prints diagnostic info on a failed assertion.
TestHelper(pred, msg) ==
    IF pred THEN "pass" ELSE msg

====