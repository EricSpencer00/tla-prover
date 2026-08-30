---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Ints

\* Intersection of two sets as a plain TRUE/FALSE test (not a set-valued result).
Overlaps(s, t) == \E x \in s : x \in t

MaxOf(s) == CHOOSE x \in s : \A y \in s : y <= x
MinOf(s) == CHOOSE x \in s : \A y \in s : y >= x

\* Generic reduction of a set with an accumulator and binary operator.
SetReduce(f, s, base) ==
  LET iter[T \in SUBSET s] ==
        IF T = {} THEN base
        ELSE LET x == CHOOSE y \in T : TRUE
             IN f(x, iter[T \ {x}])
  IN iter[s]

\* Sequence reduction (fold) via the library's SeqFold operator.
SeqReduce(f, seq, base) == SeqFold(f, seq, base)

IndexOf(seq, e) ==
  CHOOSE idx \in 1..Len(seq) : seq[idx] = e

SeqSet(seq) == { seq[i] : i \in 1..Len(seq) }

LastOf(seq) == seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

RemoveAll(seq, e) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

IntersectOfSets(S) ==
  CHOOSE x \in S :
    \A y \in S : (\A z \in x : z \in y)

Permutations(s) ==
  LET rec[T \in SUBSET s] ==
        IF T = {} THEN { <<>> }
        ELSE { <<x>> \o p : x \in T, p \in rec[T \ {x}] }
  IN rec[s]

\* Test helper: prints the expressions if the test fails, then turns FALSE.
Test(e1, e2) == e1 = e2 \/ (PrintT("Test failed: "), PrintT(e1), PrintT(" vs "), PrintT(e2), FALSE)

CONSTANTS Spec
Init == TRUE
Next == TRUE
Spec == Spec /\ Init /\ [][Next]_Spec
====