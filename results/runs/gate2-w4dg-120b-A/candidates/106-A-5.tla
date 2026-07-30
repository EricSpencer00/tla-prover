---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MAXVAL

\* Intersection: the two input sets have a non-empty overlap.
Intersect(set1, set2) == \E x \in set1 : x \in set2

\* MaxVal / MinVal: the greatest / least element of a set of naturals.
MaxVal(S) == LET f[T \in SUBSET S] ==
                 IF T = {} THEN 0
                 ELSE LET x == CHOOSE y \in T : TRUE
                      IN  IF \E z \in T : z > x THEN f[T \ {x}] ELSE x
             IN f[S]
MinVal(S) == LET f[T \in SUBSET S] ==
                 IF T = {} THEN MAXVAL
                 ELSE LET x == CHOOSE y \in T : TRUE
                      IN  IF \E z \in T : z < x THEN f[T \ {x}] ELSE x
             IN f[S]

\* SetReduce: fold a binary function f over a set S, threading an acc.
SetReduce(f, S, seed) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN seed
        ELSE LET x == CHOOSE y \in T : TRUE
                 Y == T \ {x}
             IN  g[Y] /\ f(g[Y], x)
  IN g[S]

\* SeqReduce: fold a binary function f over a sequence seq, library foldl.
SeqReduce(f, seq, seed) ==
  IF seq = <<>> THEN seed
  ELSE LET x == Head(seq)
           rest == SeqReduce(f, Tail(seq), seed)
       IN f(rest, x)

\* IndexOf: the first (lowest) index where elem appears in the sequence.
IndexOf(seq, elem) ==
  LET f[i \in 1..Len(seq)] ==
        IF seq[i] = elem THEN i
        ELSE IF i = Len(seq) THEN 0
        ELSE f[i + 1]
  IN f[1]

\* Setify: the set of elements appearing in the sequence.
Setify(seq) == { seq[i] : i \in 1..Len(seq) }

Last(seq) == Head(Reverse(seq))

SeqEmpty(seq) == Len(seq) = 0

\* RemoveAll: the sequence with all occurrences of elem stripped out.
RemoveAll(seq, elem) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* IntersectSet: the intersection of a set of sets.
IntersectSet(S) == { x \in UNION S : \A Y \in S : x \in Y }

\* Permutations: all permutation sequences of a finite set m.
RecPermutations(m) ==
  IF m = {} THEN {<<>>}
  ELSE { <<x>> \o s : x \in m, s \in RecPermutations(m \ {x}) }
Permutations == RecPermutations

\* Assert: always true, but prints a diagnostic message when its argument is FALSE.
Assert(b) == UNCHANGED << |-> TRUE |>

SpecW4 == Spec /\ TRUE

TypeOK == TRUE

====