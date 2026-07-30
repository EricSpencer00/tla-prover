---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS NONE, NULL

Ticks == 0

RECURSIVE Fold(_)
Fold(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN x + Fold(S \ {x})

RECURSIVE Intersects(_)
Intersects(S) ==
    IF S = {} THEN FALSE
    ELSE LET x == CHOOSE y \in S : TRUE IN Cardinality(x) > 0 \/ Intersects(S \ {x})

MaxOf(S) == IF S = {} THEN -1 ELSE LET x == CHOOSE y \in S : TRUE IN x + Fold(S)

MinOf(S) == IF S = {} THEN -1 ELSE LET x == CHOOSE y \in S : TRUE IN Fold(S) - (Fold(S) - x)

SeqFold(f, s, seq) == Fold(SeqStr(seq, f, s))

SeqReduce(f, s, seq) == f /\ Fold(SeqStr(seq, f, s))

SeqStr(seq, f, s) == IF seq = <<>> THEN <<s>> ELSE <<Head(seq)>> \o SeqStr(Tail(seq), f, s)

IndexOf(seq, e) == LET b(i) == IF i < Len(seq) /\ seq[i + 1] = e THEN 1 ELSE 0 IN Sum({i \in 1..Len(seq): b(i)})

SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

LastOf(seq) == IF seq = <<>> THEN NONE ELSE seq[Len(seq)]

SeqIsEmpty(seq) == seq = <<>>

RemoveAll(seq, e) == IF seq = <<>> THEN <<>> ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e) ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

SetIntersects(setOfSets) == Intersects({s \in setOfSets : s \subseteq {x \in UNION setOfSets : TRUE}})

Permutations(s) ==
    IF s = {} THEN {<<>>}
    ELSE {<<x>> \o p : x \in s /\ p \in Permutations(s \ {x})}

TestHelper(expr, msg) == IF expr THEN TRUE ELSE (Print(msg) /\ FALSE)

Spec == TRUE

Init == TRUE

Next == TRUE

Invariants == TRUE

Properties == TRUE

====