---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MinInt, MaxInt, Elements

VARIABLES seq, s

vars == <<seq, s>>

\* Set intersection: a test that two sets have a non-empty overlap.
Intersection(a, b) == \E x \in a : x \in b

\* Maximum element of a set, defined by folding the set with the max
\* function, seeded at the lowest possible value.
REDMAX(X) == LET f[T \in SUBSET X] ==
                  IF T = {} THEN MinInt
                  ELSE LET y == CHOOSE e \in T : TRUE
                       IN  IF y > f[T \ {y}] THEN y ELSE f[T \ {y}]
             IN f[X]

\* Minimum element of a set, defined by folding the set with the min
\* function, seeded at the highest possible value.
REDMIN(X) == LET f[T \in SUBSET X] ==
                  IF T = {} THEN MaxInt
                  ELSE LET y == CHOOSE e \in T : TRUE
                       IN  IF y < f[T \ {y}] THEN y ELSE f[T \ {y}]
             IN f[X]

\* Generalized set reduction: fold the set X with binary function g,
\* seeding the accumulator at the value a.
REDSET(g, a, X) == LET f[T \in SUBSET X] ==
                       IF T = {} THEN a
                       ELSE LET y == CHOOSE e \in T : TRUE
                            IN  g[y, f[T \ {y}]]
                  IN f[X]

\* Generalized sequence reduction: fold the sequence X with binary
\* function g, seeding the accumulator at the value a, using a library
\* fold operator.
REDFOL(g, a, X) == Fold(g, X, a)

\* Find the index of element e in the sequence seq, or -1 if it is not
\* present.
Find(seq, e) ==
    LET f[i \in 1..Len(seq)] ==
          IF seq[i] = e THEN i
          ELSE IF i = Len(seq) THEN 0
          ELSE f[i + 1]
    IN f[1] - 1

\* Set-of-elements: convert a sequence into the set of its members.
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Retrieve the last element from a sequence.
Last(seq) == IF seq = <<>> THEN CHOOSE e \in Elements : TRUE ELSE seq[Len(seq)]

\* IsEmpty: a boolean test on whether a sequence is empty.
IsEmpty(seq) == seq = <<>>

\* RemoveAll: delete every occurrence of element e from a sequence.
RemoveAll(seq, e) == FILTER [x \in seq |-> x] : x # e

\* Set intersection: fold a set of sets with the set-intersection
\* operator, using universal set as the seed.
IntersectSetOfSets(sets) == REDSET([x, y \in 1..Cardinality(sets) |-> sets[x] \cap sets[y]], Elements, 1..Cardinality(sets))

\* Permutations: generate all permutation sequences of a finite set.
Permutations(S) ==
    LET f[T \in SUBSET S] ==
          IF T = {} THEN {<<>>}
          ELSE LET y == CHOOSE e \in T : TRUE
               IN { <<y>> # s \in f[T \ {y}] : s }
    IN f[S]

\* TestHelper: a helper operator for writing assertions that prints
\* diagnostic information on failure.
TestHelper(cond, m) == IF cond THEN "ok" ELSE m

Spec == TRUE
Init == TRUE
Next == TRUE
TypeOK == TRUE
StateConstraint == TRUE
NextStateConstraint == TRUE
SpecInv == TRUE

====