---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxEl, MaxSeq

VARIABLES seq

vars == <<seq>>

TypeOK ==
  /\ seq \in Seq(1 .. MaxEl)

Init ==
  /\ seq = << >>

InRange(s, start, step) ==
  /\ start <= step + start
  /\ \A i \in 0 .. step : start + i \in s

\* (1) Set intersection test: two sets overlap iff they share a member.
\* (2) Maximum/minimum element selection from a set (folded over the set).
\* (3) Generalized set reduction (fold over a set with an accumulator).
\* (4) Sequence reduction (fold over a sequence with an accumulator, via FoldSeq).
\* (5) Find the index of an element in a sequence.
\* (6) Convert a sequence to the set of its elements.
\* (7) Get the last element of a sequence.
\* (8) Test if a sequence is empty.
\* (9) Remove all occurrences of an element from a sequence.
\* (10) Intersection of a set of sets.
\* (11) Generate all permutation sequences of a finite set.
\* (12) Test helper that prints diagnostics on failure.
UtilOps ==
  [ Intersect ==
      /\ \E s, t \in SUBSET (1 .. MaxEl) :
           /\ Cardinality(s) > 0
           /\ Cardinality(t) > 0
           /\ s \cap t # {}
      /\ Cardinality(s) <= MaxEl
    , MaxOf ==
      /\ \E s \in SUBSET (1 .. MaxEl) :
           /\ s # {}
           /\ s \subseteq (1 .. MaxEl)
           /\ LET g[T \in SUBSET (1 .. MaxEl)] ==
                  IF T = {} THEN 0
                  ELSE LET x == CHOOSE y \in T : TRUE IN x + g[T \ {x}]
              IN g[s]
    , MinOf ==
      /\ \E s \in SUBSET (1 .. MaxEl) :
           /\ s # {}
           /\ s \subseteq (1 .. MaxEl)
           /\ LET g[T \in SUBSET (1 .. MaxEl)] ==
                  IF T = {} THEN MaxEl + 1
                  ELSE LET x == CHOOSE y \in T : TRUE IN x + g[T \ {x}]
              IN g[s]
    , FoldSet ==
      /\ \E s \in SUBSET (1 .. MaxEl), op \in {+} :
           LET g[T \in SUBSET (1 .. MaxEl)] ==
                IF T = {} THEN 0
                ELSE LET x == CHOOSE y \in T : TRUE IN op[x, g[T \ {x}]]
           IN g[s] = Cardinality(s)
    , FoldSeq ==
      /\ \E s \in Seq(1 .. MaxEl), op \in {+} :
           FoldSeq(s, op, 0) = Cardinality({s[i] : i \in DOMAIN s})
    , IndexOf ==
      /\ \E s \in Seq(1 .. MaxEl), x \in 1 .. MaxEl :
           LET g[i \in DOMAIN s \cup {0}] ==
                IF i = 0 THEN 0
                ELSE IF s[i] = x THEN i
                ELSE g[i - 1]
           IN g[Len(s)] > 0
    , ToSet ==
      /\ \E s \in Seq(1 .. MaxEl) : {s[i] : i \in DOMAIN s} = (1 .. MaxEl)
    , Last ==
      /\ \E s \in Seq(1 .. MaxEl) : Len(s) > 0 => s[Len(s)] \in 1 .. MaxEl
    , IsEmpty ==
      /\ \E s \in Seq(1 .. MaxEl) : Len(s) = 0 <=> s = << >>
    , Remove ==
      /\ \E s \in Seq(1 .. MaxEl), x \in 1 .. MaxEl :
           LET g[i \in DOMAIN s \cup {0}] ==
                IF i = 0 THEN << >>
                ELSE IF s[i] = x THEN g[i - 1] ELSE Append(g[i - 1], s[i])
           IN g[Len(s)]
    , IntersectMany ==
      /\ \E S \in SUBSET SUBSET (1 .. MaxEl) :
           /\ S # {}
           /\ Cardinality(S) >= 2
           /\ LET g[T \in SUBSET SUBSET (1 .. MaxEl)] ==
                IF T = {} THEN (1 .. MaxEl)
                ELSE LET x == CHOOSE y \in T : TRUE IN x \cap g[T \ {x}]
              IN g[S] # {}
    , Permutations ==
      /\ \E s \in SUBSET (1 .. MaxEl) :
           /\ s # {}
           /\ LET g[T \in SUBSET (1 .. MaxEl)] ==
                IF T = {} THEN {<< >>}
                ELSE UNION { Append(p, x) : x \in T, p \in g[T \ {x}] }
              IN \A p \in g[s] : Len(p) = Cardinality(s)
    , TestHelper ==
      /\ LET a == 1 + 1
         b == 2
      IN
        /\ a = b
        /\ Cardinality({a, b}) = 1
  ]

Spec == UtilOps

====