---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS

Spec == "Spec"
InitSpec == "InitSpec"
NextSpec == "NextSpec"
SpecInv == "SpecInv"
SpecProps == "SpecProps"

NoSeq == "NoSeq"

\* Set intersection test: true iff the two sets share at least one element.
SetIntersect(S, T) == S \cap T # {}

\* Maximum element of a non-empty set of naturals, reduced via a fold-like
\* helper that works for any function with an identity element.
SetMax(S) == CHOOSE m \in S : \A x \in S : x <= m

SetMin(S) == CHOOSE m \in S : \A x \in S : m <= x

SetFold(f, S, base) ==
  LET rec[E \in SUBSET S] ==
        IF E = {} THEN base
        ELSE LET x == CHOOSE y \in E : TRUE IN f[x, rec[E \ {x}]]
  IN rec[S]

\* Sequence reduction (fold) using the library's FoldSeq operator.
SeqFold(f, seq, base) == FoldSeq(f, base, seq)

SeqIndex(seq, x) ==
  CHOOSE k \in DOMAIN seq : seq[k] = x

SeqToSet(seq) == { seq[k] : k \in DOMAIN seq }

SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == seq = << >>

SeqErase(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

SetIntersectAll(T) ==
  IF T = {} THEN {}
  ELSE CHOOSE S \in T : \A U \in T : S \subseteq U

\* Generate all permutations of a finite set of natural keys, returned as a
\* set of sequences (order matters, so each distinct ordering appears once).
Permutations(S) ==
  IF S = {} THEN {<< >>}
  ELSE { AppendSeq(p, <<x>>): x \in S, p \in Permutations(S \ {x}) }

\* Test helper: asserts a condition and, if it fails, prints a diagnostic
\* string before aborting the model check.
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE UNCHANGED <<>> /\ PrintT(msg)
====