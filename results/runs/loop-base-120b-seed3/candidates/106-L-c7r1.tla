---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

VARIABLE dummy

Init == dummy = 0

Next == dummy' = dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

(* Utility operators *)

Overlap(S, T) == \E x \in S : x \in T

SetMax(S) == 
    IF S = {} THEN NULL 
    ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
    IF S = {} THEN NULL 
    ELSE CHOOSE x \in S : \A y \in S : y >= x

SetFold(S, init, f) ==
    IF S = {} THEN init
    ELSE 
        LET x == CHOOSE y \in S : TRUE
            Rest == S \ {x}
        IN SetFold(Rest, f(init, x), f)

SeqFold(seq, init, f) == FoldSeq(seq, init, f)

SeqIndexOf(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN Min({ i \in 1..Len(seq) : seq[i] = elem })
    ELSE -1

SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

SeqLast(seq) == 
    IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

SeqIsEmpty(seq) == Len(seq) = 0

SeqRemoveAll(seq, e) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF seq[1] = e
         THEN SeqRemoveAll(SubSeq(seq, 2, Len(seq)), e)
         ELSE <<seq[1]>> \o SeqRemoveAll(SubSeq(seq, 2, Len(seq)), e)

SetIntersection(SS) == { x \in UNION SS : \A A \in SS : x \in A }

Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { { <<e>> \o p } : e \in S, p \in Permutations(S \ {e}) }

Print(msg) == msg

AssertHelper(cond, msg) == cond \/ (Print(msg) /\ FALSE)

====