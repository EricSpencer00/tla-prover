---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

SetOverlap(S, T) == 
    \E x \in S : x \in T

SetMax(S) == 
    IF S = {} THEN NULL 
    ELSE CHOOSE x \in S : \A y \in S : x >= y

SetMin(S) == 
    IF S = {} THEN NULL 
    ELSE CHOOSE x \in S : \A y \in S : x <= y

\* Generalized set reduction (fold) over a set
RECURSIVE SetReduce(_,_ ,_)
SetReduce(S, f, a) == 
    IF S = {} THEN a 
    ELSE LET x == CHOOSE y \in S : TRUE 
         IN SetReduce(S \ {x}, f, f(a, x))

\* Sequence reduction (fold) over a sequence
RECURSIVE SeqReduce(_,_ ,_)
SeqReduce(seq, f, a) == 
    IF Len(seq) = 0 THEN a 
    ELSE SeqReduce(Tail(seq), f, f(a, Head(seq)))

SeqIndex(seq, e) == 
    IF \E i \in 1..Len(seq) : seq[i] = e
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = e
    ELSE 0

SeqToSet(seq) == 
    { seq[i] : i \in 1..Len(seq) }

SeqLast(seq) == 
    IF Len(seq) = 0 THEN NULL 
    ELSE seq[Len(seq)]

SeqIsEmpty(seq) == 
    Len(seq) = 0

\* Remove all occurrences of an element from a sequence
RECURSIVE SeqRemoveAll(_,_)
SeqRemoveAll(seq, e) == 
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = e 
         THEN SeqRemoveAll(Tail(seq), e)
         ELSE << Head(seq) >> \o SeqRemoveAll(Tail(seq), e)

SetIntersectionAll(S) == 
    INTERSECTION(S)

\* Generate all permutations of a finite set
RECURSIVE Permutations(_)
Permutations(S) == 
    IF S = {} THEN { << >> }
    ELSE UNION { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

\* Assertion helper that prints a message on failure (TLC will output the message)
Assert(pred, msg) == 
    IF pred THEN TRUE ELSE (Print(msg) /\ FALSE)

\* ----------------------------------------------------------------------
\* Trivial specification scaffolding (required identifiers)
\* ----------------------------------------------------------------------

SPECIFICATION == TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == {}

PROPERTIES == {}

====