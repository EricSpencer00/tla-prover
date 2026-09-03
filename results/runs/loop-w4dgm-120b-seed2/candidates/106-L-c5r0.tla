---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS PermutationsOf

Spec == "Specification placeholder"
Init == "Init placeholder"
NextState == "Next placeholder"
VarsInvariant == "VarsInvariant placeholder"
TypeOK == "TypeOK placeholder"

\* set intersection test: true iff s1 and s2 have a common element
Intersect(s1, s2) == \E x \in s1 : x \in s2

\* maximum and minimum element selection from a nonempty set of naturals
MaxElem(s) == CHOOSE x \in s : \A y \in s : y <= x
MinElem(s) == CHOOSE x \in s : \A y \in s : x <= y

\* generalized set reduction (fold) with an accumulator and binary operation op
FoldSet(s, init, op) ==
  LET
    g[T \in SUBSET s] ==
      IF T = {} THEN init
      ELSE LET x == CHOOSE y \in T : TRUE
               rest == g[T \ {x}]
           IN op[x, rest]
  IN g[s]

\* sequence reduction (fold) using the library FoldSeq operator
FoldSeq(seq, init, op) == FoldSeq(seq, init, op)

\* find the index of element x in a sequence seq, or 0 if absent
IndexOf(seq, x) == CHOOSE k \in 0..Len(seq) : (k = 0 \/ seq[k] = x) /\ \A j \in 1..Len(seq) : seq[j] = x => j = k

\* convert a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* get the last element of a nonempty sequence
LastOf(seq) == seq[Len(seq)]

\* test if a sequence is empty
SeqEmpty(seq) == Len(seq) = 0

\* remove all occurrences of x from a sequence seq
RemoveAll(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN RemoveAll(Tail(seq), x)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), x)

\* set intersection of a set-of-sets
IntersectSets(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN x \cap IntersectSets(S \ {x})

\* generate all permutations of a finite set s as sequences
Permutations(s) ==
  { p \in PermutationsOf : SeqToSet(p) = s }

\* test helper that prints diagnostic information on assertion failure
TestHelper(pred, msg) == IF pred THEN TRUE ELSE (msg /\ FALSE)

====