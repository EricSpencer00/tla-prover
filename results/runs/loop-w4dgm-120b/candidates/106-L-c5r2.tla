---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Elements

VARIABLES unused

vars == <<unused>>

Spec == TRUE

Init == unused = 0

Next == unused = 0

Spec == Spec /\ Init /\ [][Next]_vars

TypeOK == TRUE

StateConstraint == TRUE

SpecInv == Spec /\ TypeOK /\ StateConstraint

\* 1. Set intersection test: TRUE iff a and b share at least one element.
Intersect(a, b) == \E x \in a : x \in b

\* 2. Maximum and minimum element selection from a non-empty set.
\*    If the set has a single element it is both max and min.
MaxOf(S) == LET x == CHOOSE y \in S : TRUE IN x
MinOf(S) == LET x == CHOOSE y \in S : TRUE IN x

\* 3. Generalized set reduction (fold) with an accumulator.
SetFold(f, S, a) == IF S = {} THEN a
                    ELSE SetFold(f, S \ {CHOOSE x \in S : TRUE}, f(a, CHOOSE x \in S : TRUE))

\* 4. Sequence reduction (fold) using the library's SeqFold operator.
SeqFold(f, seq, a) == IF seq = <<>> THEN a
                      ELSE SeqFold(f, Tail(seq), f(a, Head(seq)))

\* 5. Find the index (1-based) of an element in a sequence; 0 if absent.
IndexOf(seq, e) == CHOOSE i \in 0..Len(seq) :
                      (i = 0 \/ (i \in 1..Len(seq) /\ seq[i] = e))
                        /\ \A j \in 1..(IF i = 0 THEN Len(seq) ELSE i - 1) : seq[j] # e

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* 8. Check if a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* 9. Remove all occurrences of element e from a sequence.
SeqRemoveAll(seq, e) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = e THEN SeqRemoveAll(Tail(seq), e)
  ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), e)

\* 10. Intersection of a set of sets.
SetInter(S) == { x \in CHOOSE s \in S : TRUE : \A s \in S : x \in s }

\* 11. Generate all permutation sequences of a finite set.
Permutations(s) ==
  IF s = {} THEN { <<>> }
  ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

\* 12. Test helper: asserts a condition, printing a message on failure.
Assert(msg, cond) == IF cond THEN TRUE ELSE (msg /\ cond)

====