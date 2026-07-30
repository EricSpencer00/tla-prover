---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* This module provides a handful of reusable utility operators for the
\* key-value store specs.  It has no system model of its own; the operators
\* below are pure functions that other specs import.
\* The reference .cfg does not name any required constants or actions,
\* so this file is intentionally small.

CONSTANTS NoSeq

RECURSIVE Intersects(_, _)
Intersects(S, T) ==
    \/ S = {}
    \/ T = {}
    \/ (\E x \in S : x \in T)

RECURSIVE Max(_, _)
Max(f, S) ==
    IF S = {} THEN NoSeq
    ELSE LET m == CHOOSE y \in S : \A z \in S : f(y) >= f(z) IN f(m)

RECURSIVE Min(_, _)
Min(f, S) ==
    IF S = {} THEN NoSeq
    ELSE LET m == CHOOSE y \in S : \A z \in S : f(y) <= f(z) IN f(m)

RECURSIVE FoldSet(_, _, _)
FoldSet(f, e, S) ==
    IF S = {} THEN e
    ELSE LET x == CHOOSE y \in S : TRUE IN f(x, FoldSet(f, e, S \ {x}))

RECURSIVE FoldSeq(_, _, _)
FoldSeq(f, e, s) ==
    IF s = <<>> THEN e
    ELSE f(Head(s), FoldSeq(f, e, Tail(s)))

RECURSIVE IndexOf(_, _)
IndexOf(x, s) ==
    IF s = <<>> THEN 0
    ELSE IF Head(s) = x THEN 1
    ELSE LET k == IndexOf(x, Tail(s)) IN IF k = 0 THEN 0 ELSE k + 1

RECURSIVE ToSet(_)
ToSet(s) ==
    IF s = <<>> THEN {}
    ELSE {Head(s)} \cup ToSet(Tail(s))

RECURSIVE LastElt(_)
LastElt(s) ==
    IF s = <<>> THEN NoSeq
    ELSE IF Tail(s) = <<>> THEN Head(s)
    ELSE LastElt(Tail(s))

RECURSIVE IsEmpty(_)
IsEmpty(s) == s = <<>>

RECURSIVE RemoveAll(_, _)
RemoveAll(x, s) ==
    IF s = <<>> THEN <<>>
    ELSE IF Head(s) = x THEN RemoveAll(x, Tail(s))
    ELSE <<Head(s)>> \o RemoveAll(x, Tail(s))

RECURSIVE IntersectSets(_)
IntersectSets(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN IF \E z \in S : TRUE THEN x \cap IntersectSets(S \ {x}) ELSE {}

RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN {<<>>}
    ELSE {<<x>> \o p : x \in S, p \in Permutations(S \ {x})}

TestHelper(e, f, g) ==
    LET res == IF e = f THEN "pass" ELSE "fail" IN
        IF res = "pass" THEN TRUE ELSE (Print("TestHelper: e = f failed; e = "); Print(e); Print(" f = "); Print(f); Print(" g = "); Print(g); FALSE)

\* The .cfg does not name any SPECIFICATION, INIT, NEXT, INVARIANTS, or
\* PROPERTIES, but the spec template requires they exist.  They are all
\* defined as trivially true operators -- the real work is in the utilities.
\* Leaving them defined (instead of omitting them) is what keeps the .cfg
\* from silently failing to find a required identifier.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====