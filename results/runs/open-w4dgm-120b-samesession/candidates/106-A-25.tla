---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Intersection test for two sets.
Intersect(a, b) == \E x \in a : x \in b

\* Max/min selector for a non-empty set of naturals.
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Generalized set reduction (fold) with an accumulator.
ReduceSet(S, f, init) ==
  LET
    rec(T) == IF T = {} THEN init
              ELSE LET x == CHOOSE y \in T : TRUE IN f[x, rec(T \ {x})]
  IN rec(S)

\* Sequence reduction using a library fold operator.
ReduceSeq(sq, f, init) == FoldSeq(f, init, sq)

\* Index of an element in a sequence, or 0 if absent.
SeqFind(sq, e) ==
  LET g[i \in DOMAIN sq] == IF sq[i] = e THEN i ELSE 0
  IN ReduceSeq([i \in DOMAIN sq |-> g[i]], (a, b) -> IF a > b THEN a ELSE b, 0)

\* Convert a sequence to the set of its elements.
SeqAsSet(sq) == { sq[i] : i \in DOMAIN sq }

\* Last element of a non-empty sequence.
SeqLast(sq) == sq[Len(sq)]

\* Empty-sequence test.
SeqEmpty(sq) == sq = << >>

\* Remove all occurrences of an element from a sequence.
SeqRemoveAll(sq, e) ==
  [i \in 1..(Len(sq) - Cardinality({i \in DOMAIN sq : sq[i] = e}))
    |-> CHOOSE k \in DOMAIN sq :
         Cardinality({j \in DOMAIN sq : sq[j] = e /\ j <= k})
           = Cardinality({j \in DOMAIN sq : sq[j] = e /\ j < i}) /\ sq[k] # e]

\* Intersection of a set of sets.
IntersectAll(F) == { x \in UNION F : \A S \in F : x \in S }

\* Permutation generation for a finite set via prefix extension.
RecPerms(S, pref) ==
  IF S = {} THEN {pref}
  ELSE UNION { RecPerms(S \ {e}, Append(pref, e)) : e \in S }
Permutations(S) == RecPerms(S, <<>>)

\* Print-diagnostic helper for assertions (no effect at runtime).
Print(msg) == msg

====