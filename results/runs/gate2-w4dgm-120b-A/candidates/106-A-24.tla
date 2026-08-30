---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS MaxVal

\* set intersection: True iff a and b overlap
Intersect(a, b) == \E x \in a : x \in b

\* reduce a set using a binary op, folding an accumulator over its elements
SetReduce(S, f, init) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == T \ {x}
             IN f(g[rest], x)
  IN g[S]

\* reduce a sequence using a binary op, folding an accumulator over its elements
SeqReduce(sq, f, init) == FoldL(f, init, sq)

\* find the index of x in sequence sq (1-based), or 0 if absent
IndexOf(x, sq) ==
  LET g[i \in 1..Len(sq)] ==
        IF sq[i] = x THEN i
        ELSE IF i = Len(sq) THEN 0
        ELSE g[i + 1]
  IN g[1]

\* convert a sequence to the set of its elements
SeqToSet(sq) == { sq[i] : i \in 1..Len(sq) }

\* test helper: uses WHEN to avoid evaluating the body unless the condition fails
Assert(expr, msg) == WHEN ~expr \in BOOLEAN /\ expr = FALSE /\ msg \in STRING THEN TRUE

\* permutation of a finite set via backtracking over an array of picks
PermutationEnum(A) ==
  /\ \E picks \in 1..Cardinality(A) -> A :
        /\ \A i \in 1..Cardinality(A) : picks[i] \in A
        /\ \A i, j \in 1..Cardinality(A) : i # j => picks[i] # picks[j]
  /\ picks

\* remove all occurrences of x from sequence sq
SeqRemoveAll(x, sq) ==
  LET f(a, y) == IF y = x THEN a ELSE Append(a, y)
  IN SeqReduce(sq, f, << >>)
====