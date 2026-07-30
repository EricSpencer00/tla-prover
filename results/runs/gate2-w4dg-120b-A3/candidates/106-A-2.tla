---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences, TLC

\* A utility library for the key-value store specs.  All of its operators are
\* pure, with no state of their own; the spec below exists only so the
\* operators are reachable by the TLC configuration, which names them.
CONSTANTS NONE

RECURSIVE Intersects(_)
Intersects(S) ==
  IF S = {} THEN FALSE
  ELSE LET x == CHOOSE y \in S : TRUE IN x \in S \ {x}

RECURSIVE MaxSet(_)
MaxSet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN IF \E z \in S : z > x THEN MaxSet(S \ {x}) ELSE x

RECURSIVE MinSet(_)
MinSet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN IF \E z \in S : z < x THEN MinSet(S \ {x}) ELSE x

RECURSIVE ReduceSet(_)
ReduceSet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + ReduceSet(S \ {x})

RECURSIVE IndexOf(_)
IndexOf(s, x) ==
  IF s = << >> THEN 0
  ELSE IF Head(s) = x THEN 1
  ELSE LET i == IndexOf(Tail(s), x) IN IF i = 0 THEN 0 ELSE i + 1

RECURSIVE IntersectSets(_)
IntersectSets(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN x \cap IntersectSets(S \ {x})

RECURSIVE PermuteSeq(_)
PermuteSeq(S) ==
  IF S = {} THEN {<< >>}
  ELSE {<<x>> \o s : x \in S, s \in PermuteSeq(S \ {x})}

VARIABLES dummy
vars == << dummy >>

TypeOK == TRUE

Init == dummy = NONE
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

SpecCitation == Spec
InitCitation == Init
NextCitation == Next

====