---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  Utility library providing common helper operators for the key-value    *)
(*  store specifications.                                                 *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\* Set intersection test: Overlaps(s, t) is TRUE iff the two sets have
\* at least one element in common.
\* ----------------------------------------------------------------------
Overlaps(s, t) == 
    \E x \in s : x \in t

\* ----------------------------------------------------------------------
\* Maximum element of a non‑empty finite set.
\* ----------------------------------------------------------------------
Max(s) ==
    /\ s # {}
    /\ \E m \in s : \A x \in s : x <= m

\* ----------------------------------------------------------------------
\* Minimum element of a non‑empty finite set.
\* ----------------------------------------------------------------------
Min(s) ==
    /\ s # {}
    /\ \E m \in s : \A x \in s : x >= m

\* ----------------------------------------------------------------------
\* Generalized set reduction (fold) using an accumulator.  If the set is
\* empty the initial accumulator value is returned.
\* The reduction function f must be a total binary operator.
\* ----------------------------------------------------------------------
SetReduce(s, init, f) ==
    IF s = {}
        THEN init
        ELSE LET
                elems == CHOOSE seq \in Seq(s) : Len(seq) = Cardinality(s)
                Rec(i) ==
                    IF i = 1 THEN f[init, elems[i]]
                    ELSE f[Rec(i-1), elems[i]]
             IN Rec(Len(elems))

\* ----------------------------------------------------------------------
\* Sequence reduction (fold) using an accumulator.
\* The reduction function f must be a total binary operator.
\* ----------------------------------------------------------------------
SeqReduce(seq, init, f) ==
    IF Len(seq) = 0
        THEN init
        ELSE LET
                Rec(i) ==
                    IF i = 1 THEN f[init, seq[1]]
                    ELSE f[Rec(i-1), seq[i]]
             IN Rec(Len(seq))

\* ----------------------------------------------------------------------
\* Find the index of element e in sequence s (1‑based).  Returns 0 if e
\* does not occur in s.
\* ----------------------------------------------------------------------
SeqIdx(s, e) ==
    IF e \in SeqToSet(s)
        THEN CHOOSE i \in 1..Len(s) : s[i] = e
        ELSE 0

\* ----------------------------------------------------------------------
\* Convert a sequence to the set of its elements.
\* ----------------------------------------------------------------------
SeqToSet(s) ==
    { s[i] : i \in 1..Len(s) }

\* ----------------------------------------------------------------------
\* Get the last element of a non‑empty sequence.
\* ----------------------------------------------------------------------
Last(s) ==
    s[Len(s)]

\* ----------------------------------------------------------------------
\* Test whether a sequence is empty.
\* ----------------------------------------------------------------------
SeqIsEmpty(s) ==
    Len(s) = 0

\* ----------------------------------------------------------------------
\* Remove all occurrences of element e from sequence s.
\* ----------------------------------------------------------------------
SeqRemoveAll(s, e) ==
    [ i \in 1..(Len(s) - Cardinality({ j \in 1..Len(s) : s[j] = e })) |-> 
        s[ i + Cardinality({ j \in 1..i : s[j] = e }) ] ]

\* ----------------------------------------------------------------------
\* Intersection of a set of sets.  The argument must be a set whose
\* elements are themselves sets.
\* ----------------------------------------------------------------------
SetIntersection(ss) ==
    IF ss = {}
        THEN {}
        ELSE \A s \in ss : s

\* ----------------------------------------------------------------------
\* Generate all permutation sequences of the finite set s.
\* ----------------------------------------------------------------------
Permutations(s) ==
    IF s = {}
        THEN { << >> }
        ELSE UNION { << e >> \o p : e \in s, p \in Permutations(s \ {e}) }

\* ----------------------------------------------------------------------
\* Test helper that asserts a condition and prints a diagnostic message
\* when the condition is FALSE.  The specification checks that the
\* expression Test(cond, msg) always evaluates to TRUE.
\* ----------------------------------------------------------------------
Test(cond, msg) ==
    IF cond
        THEN TRUE
        ELSE Print(msg) /\ FALSE

(***************************************************************************)
(*  Specification skeleton – the module is a pure library, but the         *)
(*  following operators are defined so that the reference .cfg can refer   *)
(*  to them without error.                                                *)
(***************************************************************************)

SPECIFICATION == TRUE

INIT == TRUE

NEXT == UNCHANGED {}

INVARIANTS == {}

PROPERTIES == {}

=============================================================================