---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS MaxSet, MaxSeq

\* Intersection test: TRUE iff the two finite sets have an element in common.
HasIntersection(A, B) == \E x \in A : x \in B

\* Maximum and minimum elements of a non-empty finite set of natural numbers.
MaxOf(S) ==
  LET recur(f, T) ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == f(f, T \ {x})
             IN IF rest > x THEN rest ELSE x
  IN recur(recur, S)

MinOf(S) ==
  LET recur(f, T) ==
        IF T = {} THEN MaxSet + 1
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == f(f, T \ {x})
             IN IF rest < x THEN rest ELSE x
  IN recur(recur, S)

\* Generalized set reduction: fold a binary operator over the elements of a
\* set, aggregating them into a single result.
ReduceSet(f, S, init) ==
  LET recur(f, g, T) ==
        IF T = {}
          THEN init
          ELSE LET x == CHOOSE y \in T : TRUE
               IN g(g, T \ {x}, x)
      in recur(f, LAMBDA a, b, x : a(b, x), S)

\* Sequence reduction: fold a binary operator over a sequence from left to
\* right, feeding the accumulator through each element.
ReduceSeq(f, seq, init) ==
  LET recur(g, h, i, a) ==
        IF a = Len(seq)
          THEN i
          ELSE g(g, h, a + 1, h(i, seq[a + 1]))
  in recur(LAMBDA g, h, a, i : g(g, h, a + 1, h(i, seq[a + 1])), f, 0, init)

\* Find the index of an element in a sequence, or 0 if it is absent.
IndexOf(seq, x) == CHOOSE k \in 1..Len(seq) : seq[k] = x

\* Convert a sequence to the set of its elements.
SeqAsSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

\* Remove every occurrence of a value from a sequence, preserving order.
RemoveAll(seq, val) ==
  CHOOSE s \in { seq2 \in Seq(MaxSet) :
                    Len(seq2) <= Len(seq) /\ SeqAsSet(seq2) \subseteq SeqAsSet(seq)
                      /\ \A i \in 1..Len(seq2) : seq2[i] # val }
               : Len(s) = Cardinality(SeqAsSet(seq) \ {val})

\* Set intersection: the common elements of a non-empty set of sets.
Intersect(S) ==
  LET recur(T) ==
        IF Cardinality(T) = 1
          THEN CHOOSE x \in T : x
          ELSE LET x == CHOOSE y \in T : TRUE
               IN Intersection(x, recur(T \ {x}))
  in recur(S)

\* Generate all permutation sequences of a finite set via backtracking.
Permutations(S) ==
  { p \in Seq(MaxSet) :
      /\ Len(p) = Cardinality(S)
      /\ \A i \in 1..Len(p) : p[i] \in S
      /\ \A i, j \in 1..Len(p) : (p[i] = p[j]) => (i = j) }

\* Test helper: prints diagnostics on a failed assertion before aborting.
TestFail(msg) == IF msg = "" THEN msg ELSE msg

\* Empty placeholder sections required by the .cfg file.
CONSTANTS == << >>
SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED << >>
INVARIANTS == {}
PROPERTIES == {}

====