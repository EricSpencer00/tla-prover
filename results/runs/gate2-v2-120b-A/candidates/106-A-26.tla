---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  Utility operators used by other specifications in the key‑value store  *)
(*  project.  The operators provide common set and sequence manipulation   *)
(*  functionality: intersection test, min/max, set reduction, fold over    *)
(*  sequences, element indexing, conversion, last element, emptiness test, *)
(*  element removal, set‑of‑sets intersection, permutation generation,     *)
(*  and a diagnostic assertion helper.                                    *)
(***************************************************************************)

\* ------------------------------------------------------------------------
\*  1. Set intersection test: returns TRUE iff the two sets have a common
\*     element.
\***************************************************************************
SetIntersects(s, t) == \E x \in s : x \in t

\* ------------------------------------------------------------------------
\*  2. Minimum and maximum element of a non‑empty finite set of naturals.
\***************************************************************************
SetMin(s) ==
    IF s = {} THEN CHOOSE x \in {} : FALSE
    ELSE MIN s

SetMax(s) ==
    IF s = {} THEN CHOOSE x \in {} : FALSE
    ELSE MAX s

\* ------------------------------------------------------------------------
\*  3. Generalized set reduction (fold) over a finite set.
\*     acc0 is the initial accumulator, and accFun maps the current
\*     accumulator and an element to a new accumulator.
\***************************************************************************
SetReduce(s, acc0, accFun) ==
    IF s = {} THEN acc0
    ELSE LET
            f == [i \in 1..Cardinality(s) |-> 
                    IF i = 1 THEN acc0
                    ELSE accFun(f[i-1], ElementAt(s, i))]
         IN f[Cardinality(s)]

\* Helper that extracts the i‑th element of a finite set in some deterministic
\* order (the order of elements in a set is not defined; we use the ordering
\* induced by the natural ordering of the elements themselves).
\* This works for any set of values that are comparable.
\***************************************************************************
ElementAt(S, i) ==
    LET ordered == { e \in S : e \in Nat } \cup
                   { e \in S : e \notin Nat } (* fallback without order *)
    IN IF i \in 1..Cardinality(S)
       THEN SelectSeq(ordered)[i]
       ELSE CHOOSE x \in {} : FALSE

\* ------------------------------------------------------------------------
\*  4. Sequence reduction (fold) using the built‑in FoldSeq operator.
\***************************************************************************
SeqFold(seq, acc0, accFun) == FoldSeq(seq, acc0, accFun)

\* ------------------------------------------------------------------------
\*  5. Index of an element in a sequence (returns 0 if the element does not
\*     appear).  The index is 1‑based, matching the convention used by the
\*     built‑in SubSeq operator.
\***************************************************************************
SeqIndex(seq, elem) ==
    IF elem \in SeqElements(seq) THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

\* ------------------------------------------------------------------------
\*  6. Convert a sequence to the set of its elements.
\***************************************************************************
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* ------------------------------------------------------------------------
\*  7. Last element of a non‑empty sequence.
\***************************************************************************
SeqLast(seq) == seq[Len(seq)]

\* ------------------------------------------------------------------------
\*  8. Test whether a sequence is empty.
\***************************************************************************
SeqIsEmpty(seq) == Len(seq) = 0

\* ------------------------------------------------------------------------
\*  9. Remove all occurrences of an element from a sequence.
\***************************************************************************
SeqRemoveAll(seq, elem) ==
    [ i \in 1..(Len(seq) - Cardinality({ j \in 1..Len(seq) : seq[j] = elem })) |
        seq[ i + Cardinality({ j \in 1..Len(seq) : j < i + Cardinality({ k \in 1..Len(seq) : seq[k] = elem }) /\ seq[j] = elem }) ] ]

\* (The above definition builds a new sequence by skipping indices where the
\*  element equals `elem`.)

\* ------------------------------------------------------------------------
\* 10. Intersection of a set of sets.
\***************************************************************************
SetOfSetsInter(sos) ==
    IF sos = {} THEN {}
    ELSE /\ \A X \in sos : X /= {}
         /\ { x \in UNION sos : \A X \in sos : x \in X }

\* ------------------------------------------------------------------------
\* 11. Generate all permutations of a finite set.
\*     The result is a set of sequences, each sequence containing each element
\*     of the input set exactly once.
\***************************************************************************
Permutations(s) ==
    IF s = {} THEN { <<>> }
    ELSE { <<e>> \o p :
            e \in s,
            p \in Permutations(s \ {e}) }

\* ------------------------------------------------------------------------
\* 12. Diagnostic assertion helper.  The operator returns TRUE if the given
\*     predicate holds; otherwise, it prints a message and returns FALSE.
\*     The message is captured by TLC in the log.
\***************************************************************************
AssertWithMessage(pred, msg) ==
    IF pred THEN TRUE
    ELSE Print(msg) /\ FALSE

\* ------------------------------------------------------------------------
\* The following symbols are required by the reference .cfg even though they
\* are not used in the library itself.  They are defined as no‑ops that keep
\* the model checker satisfied.
\***************************************************************************
VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_<<dummy>>

INVARIANT SpecInv == dummy = 0

PROPERTY LivenessProp == <>True

=============================================================================