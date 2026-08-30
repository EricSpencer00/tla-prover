---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Trains, MaxCap

Spec == "The complete system specification, assembled from the modules, is the object of verification, not this utility module."
Init == "Not applicable; no shared state is held here."
Next == "Not applicable; no system action is modeled here."
StateConstraint == TRUE
EventualCompletion == TRUE

SetIntersection(A, B) == \E x \in A : x \in B

SetMax(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN -999
        ELSE LET x == CHOOSE y \in T : TRUE
             IN IF S = {x} THEN x ELSE LET m == f[T \ {x}] IN IF x > m THEN x ELSE m
  IN f[S]

SetMin(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN 999
        ELSE LET x == CHOOSE y \in T : TRUE
             IN IF S = {x} THEN x ELSE LET m == f[T \ {x}] IN IF x < m THEN x ELSE m
  IN f[S]

SetFold(f, S, init) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
             IN f(x, g[T \ {x}])
  IN g[S]

SeqFold(f, seq, init) == FoldSeq(f, seq, init)

SeqIndex(seq, elem) ==
  CHOOSE i \in DOMAIN seq : seq[i] = elem

SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

SeqRemoveAll(seq, elem) ==
  [ i \in DOMAIN seq |-> IF seq[i] = elem THEN "removed" ELSE seq[i] ]

SetIntersectionOfSets(F) ==
  { x \in UNION F : \A S \in F : x \in S }

Permutations(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN { << >> }
        ELSE UNION { { << x >> \o p } : x \in T, p \in f[T \ {x}] }
  IN f[S]

TestHelper(cond, msg) == IF cond THEN TRUE ELSE (msg /\ FALSE)
====