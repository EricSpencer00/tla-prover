---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* 1. Set overlap test: true iff S and T have a common element
SetOverlap(S, T) == \E x \in S : x \in T

\* 2. Maximum and minimum element of a (non‑empty) set of numbers
SetMax(S) == 
    IF S = {} THEN NULL
    ELSE Max(S)

SetMin(S) == 
    IF S = {} THEN NULL
    ELSE Min(S)

\* 3. Generalized set reduction (fold) with an accumulator
SetReduce(S, acc, f) == 
    IF S = {} THEN acc
    ELSE LET x == CHOOSE e \in S : TRUE
         IN SetReduce(S \ {x}, f(acc, x), f)

\* 4. Sequence reduction (fold) with an accumulator
SeqReduce(seq, acc, f) == 
    IF Len(seq) = 0 THEN acc
    ELSE SeqReduce(Tail(seq), f(acc, Head(seq)), f)

\* 5. Index of an element in a sequence (1‑based, 0 if not present)
SeqIndex(seq, elem) == 
    IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

\* 6. Convert a sequence to the set of its elements
SeqToSet(seq) == { x : \E i \in 1..Len(seq) : seq[i] = x }

\* 7. Last element of a sequence (NULL if empty)
SeqLast(seq) == 
    IF Len(seq) = 0 THEN NULL
    ELSE seq[Len(seq)]

\* 8. Test whether a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Remove all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) == 
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = elem
         THEN SeqRemoveAll(Tail(seq), elem)
         ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* Helper binary operator for set intersection used by SetIntersectionOfSets
Intersect(a, b) == a \cap b

\* 10. Intersection of a set of sets
SetIntersectionOfSets(SS) == 
    IF SS = {} THEN {}
    ELSE 
        LET init == CHOOSE s \in SS : TRUE
        IN SetReduce(SS, init, Intersect)

\* 11. All permutations of a finite set
Permutations(S) == 
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper that prints a diagnostic message on failure
TestHelper(expr, msg) == 
    IF expr THEN TRUE
    ELSE (Print(msg); FALSE)

====