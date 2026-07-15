---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  Utility library for key-value store specifications                    *)
(*  Provides a collection of pure functional operators for set and       *)
(*  sequence manipulation.                                                *)
(***************************************************************************)

CONSTANTS
    \* No external constants are required for this library module.
    \* The declaration is kept to satisfy the requirement that the module
    \* contains at least one constant section.
    Dummy

VARIABLES
    \* This library does not maintain any state. The variable set is empty,
    \* but the name is required syntactically.
    \* We introduce a dummy variable that never changes.
    dummy

(***************************************************************************)
(*  State definition (trivial, because the library has no mutable state)   *)
(***************************************************************************)

Init ==
    /\ dummy = 0

Next ==
    /\ dummy' = dummy

(***************************************************************************)
(*  Safety invariant (trivial)                                            *)
(***************************************************************************)

NoChange ==
    dummy' = dummy

(***************************************************************************)
(*  Convenience definitions                                               *)
(***************************************************************************)

\* 1. Set intersection test (whether two sets overlap)
Disjoint(s, t) == s \cap t = {}

\* 2. Maximum and minimum element selection from a set
MaxSet(s) ==
    IF s = {} THEN 0
    ELSE CHOOSE x \in s : \A y \in s : y <= x

MinSet(s) ==
    IF s = {} THEN 0
    ELSE CHOOSE x \in s : \A y \in s : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetFold(F, acc, s) ==
    IF s = {} THEN acc
    ELSE
        LET x == CHOOSE y \in s : TRUE IN
        SetFold(F, F(acc, x), s \ {x})

\* 4. Sequence reduction (fold over a sequence with an accumulator,
\*    implemented via the standard library's FoldSeq operator)
SeqFold(F, acc, seq) == FoldSeq(F, acc, seq)

\* 5. Finding the index of an element in a sequence (1‑based)
IndexOf(seq, elem) ==
    IF elem \notin seq THEN 0
    ELSE
        CHOOSE i \in 1..Len(seq) : seq[i] = elem

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
SeqLast(seq) ==
    IF Len(seq) = 0 THEN 0
    ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
    [ i \in 1..(Len(seq) - CountOccurrences(seq, elem)) |-> 
        seq[ i + CountBefore(seq, elem, i) ] ]

\* Helper for SeqRemoveAll: number of occurrences of elem before position i
CountBefore(seq, elem, i) ==
    Cardinality({ j \in 1..(i-1) : seq[j] = elem })

\* Helper for SeqRemoveAll: total number of occurrences of elem in seq
CountOccurrences(seq, elem) ==
    Cardinality({ j \in 1..Len(seq) : seq[j] = elem })

\* 10. Computing the intersection of a set of sets
Intersections(SS) ==
    IF SS = {} THEN {}
    ELSE \Inter S \in SS : S

\* 11. Generating all permutation sequences of a finite set
Permutations(s) ==
    IF s = {} THEN { <<>> }
    ELSE
        UNION { 
            << x >> \o p : 
                x \in s, 
                p \in Permutations(s \ {x}) 
        }

\* 12. Test helper for writing assertions that print diagnostic information
Assert(pred, msg) ==
    IF pred THEN TRUE
    ELSE Print(msg) /\ FALSE

(***************************************************************************)
(*  Specification                                                       *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<dummy>>

(***************************************************************************)
(*  Declared identifiers required by the reference .cfg                 *)
(***************************************************************************)

SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANT NoChange
PROPERTIES Spec

====