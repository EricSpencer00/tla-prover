---- MODULE Util ----
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANTS
    \* No external constants are required for this library.

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* (1) Set intersection test: returns TRUE iff S and T share at least one element.
SetIntersect(S, T) == S \cap T # {}

\* (2) Maximum element of a finite non‑empty set.
SetMax(S) == 
    IF S = {} THEN -1
    ELSE CHOOSE x \in S : \A y \in S : y <= x

\* (2) Minimum element of a finite non‑empty set.
SetMin(S) == 
    IF S = {} THEN -1
    ELSE CHOOSE x \in S : \A y \in S : x <= y

\* (3) Generalized set reduction (fold) using an associative binary operator Op.
SetReduce(S, Init, Op) ==
    IF S = {} THEN Init
    ELSE 
        LET f == [x \in S |-> 
                     IF x = CHOOSE y \in S : TRUE 
                     THEN Op(Init, x) 
                     ELSE Op(f( {y \in S : y # x} ), x)]
        IN f(CHOOSE y \in S : TRUE)

\* (4) Sequence reduction (fold) using the library FoldSeq.
SeqReduce(seq, Init, Op) == FoldSeq(seq, Init, Op)

\* (5) Index of element e in sequence s (1‑based). Returns 0 if not present.
SeqIndex(s, e) == 
    IF e \in SeqElems(s) THEN
        CHOOSE i \in 1..Len(s) : s[i] = e
    ELSE 0

\* (6) Convert a sequence to the set of its elements.
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* (7) Last element of a non‑empty sequence.
Last(s) == 
    IF Len(s) = 0 THEN -1
    ELSE s[Len(s)]

\* (8) Test if a sequence is empty.
SeqEmpty(s) == Len(s) = 0

\* (9) Remove all occurrences of element e from sequence s.
SeqRemoveAll(s, e) == 
    << >> \o [i \in 1..Len(s) |-> IF s[i] # e THEN s[i] ELSE {}]

\* (10) Intersection of a set of sets.
SetIntersection(Sets) == 
    IF Sets = {} THEN {}
    ELSE \* start with an arbitrary member and intersect all others
         LET first == CHOOSE x \in Sets : TRUE
         IN \A y \in Sets : first \subseteq y

\* (11) Generate all permutations of a finite set S (as a set of sequences).
Permutations(S) == 
    IF S = {} THEN {<<>>}
    ELSE { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* (12) Test helper that prints a message on failure.
\* (TLC will display the value of msg when the assertion fails.)
TestHelper(condition, msg) == 
    IF condition THEN TRUE ELSE
        BEGIN
            Print(msg);
            FALSE
        END

\* ----------------------------------------------------------------------
\* Specification scaffolding required by the task description
\* ----------------------------------------------------------------------

VARIABLE dummy

Init == dummy = 0

Next == dummy' = dummy

Spec == Init /\ [][Next]_<<dummy>>

\* The required names that the .cfg expects.
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

====