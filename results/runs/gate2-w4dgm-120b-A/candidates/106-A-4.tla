---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NONE

\* Represents an empty, invalid, or otherwise-unavailable value for a domain
\* the operations here work over.  It is deliberately distinct from every
\* ordinary value the operators might otherwise return.
Unchosen == NONE

\* Returns TRUE exactly when the two sets have at least one element in common.
SetIntersect(a, b) == \E x \in a : x \in b

MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized reduction over a set: applies f (binary, set element first)
\* repeatedly while folding a running accumulator, starting from init.
SetReduce(S, f, init) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE e \in T : TRUE
                 rest == g[T \ {x}]
             IN f[x, rest]
  IN g[S]

\* Generalized reduction over a sequence: applies f (binary, sequence element
\* first) repeatedly while folding a running accumulator, starting from init.
SeqReduce(seq, f, init) ==
  LET g[i \in 0 .. Len(seq)] ==
        IF i = 0 THEN init
        ELSE f[seq[i], g[i - 1]]
  IN g[Len(seq)]

ElemIndex(seq, e) ==
  CHOOSE k \in 1 .. Len(seq) : seq[k] = e

SeqToSet(seq) ==
  { seq[k] : k \in 1 .. Len(seq) }

LastElem(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

\* Builds a new sequence by copying over everything in s that is not e,
\* preserving order, so e disappears wherever it appears.
SeqRemove(s, e) == SelectSeq(s, LAMBDA x : x # e)

\* Intersection of an arbitrary family of sets -- the result contains exactly
\* those elements that appear in every member of the family.
FamilyIntersect(F) ==
  { x \in UNION F : \A A \in F : x \in A }

\* Enumerates every permutation of the finite set S as a sequence.  The
\* recursion adds each element of T to the front of every permutation of
\* T \ {e}, which is exactly the inductive construction of permutations.
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

\* Helper: prints a diagnostic message (the expression's value) and returns
\* FALSE so it can be used as the body of a deadlock-free self-loop.
TestHelper(expr) == ~ (expr = expr) /\ expr

\* The .cfg expects these definitions to exist in every module it checks, so
\* they are defined here once and reused rather than being left undeclared.
SPECIFICATION == UNCHANGED <<>>
INIT == UNCHANGED <<>>
NEXT == UNCHANGED <<>>
INVARIANTS == {}
PROPERTIES == {}
====