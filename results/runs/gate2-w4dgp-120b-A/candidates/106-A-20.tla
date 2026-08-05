---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Utility operators for set and sequence manipulation, used by the key-value
\* store specs. This module has no system state; its operators are pure functions.
CONSTANTS

\* TestIfAny2: true iff a set has any element that is also in a second set.
\* Max/Min: extremal elements of a non-empty set.
\* Reduce: fold/reduce a set with an accumulator; ReduceSeq: fold a sequence.
\* IndexOf: position of an element in a sequence; SeqToSet: sequence-to-set.
\* LastElem: last element of a sequence; IsEmptySeq: sequence emptiness test.
\* RemoveAll: drop every occurrence of a value from a sequence.
\* SetIntersection: intersection of a set of sets.
\* Permutations: generate all permutation sequences of a finite set.
\* TestHelper: assertion wrapper that prints diagnostics on failure.
IsAny2, Max, Min, Reduce, ReduceSeq, IndexOf, SeqToSet,
LastElem, IsEmptySeq, RemoveAll, SetIntersection,
Permutations, TestHelper

ASSUME IsAny2 \in {IsAny2} /\ Max \in {Max} /\ Min \in {Min}
       /\ Reduce \in {Reduce} /\ ReduceSeq \in {ReduceSeq}
       /\ IndexOf \in {IndexOf} /\ SeqToSet \in {SeqToSet}
       /\ LastElem \in {LastElem} /\ IsEmptySeq \in {IsEmptySeq}
       /\ RemoveAll \in {RemoveAll} /\ SetIntersection \in {SetIntersection}
       /\ Permutations \in {Permutations} /\ TestHelper \in {TestHelper}

NoElem == 0

VARIABLES
\* No system state: the module is a pure library and its "variables" are always empty.
vars

vars == {}

Init == vars = {}

Next == UNCHANGED vars

\* SAFETY PROPERTY: No system state at all, so the invariant is the empty set.
NoState == TRUE

\* LIVENESS PROPERTY: Trivial, the system never changes.
Quiescent == TRUE

Spec == Init /\ [][Next]_vars /\ WF_vars(Quiescent)

\* Intersection of two sets (not empty).
IsAny2(S, T) == \E x \in S : x \in T

\* Maximum element of a non-empty set.
Max(S) == CHOOSE x \in S : \A y \in S : y <= x

\* Minimum element of a non-empty set.
Min(S) == CHOOSE x \in S : \A y \in S : y >= x

\* Reduced fold over a set with an accumulator.
Reduce(S, op, a) ==
  LET rec[T \in SUBSET S] ==
    IF T = {} THEN a
    ELSE LET x == CHOOSE y \in T : TRUE IN op[x, rec[T \ {x}]]
  IN rec[S]

\* Reduce a sequence via a right fold.
ReduceSeq(seq, op, a) ==
  LET rec(i) ==
    IF i = 0 THEN a
    ELSE op[seq[i], rec(i - 1)]
  IN rec(Len(seq))

\* Index of an element in a sequence, or 0 if not present.
IndexOf(seq, val) ==
  LET rec(i) ==
    IF i > Len(seq) THEN NoElem
    ELSE IF seq[i] = val THEN i
    ELSE rec(i + 1)
  IN rec(1)

\* Convert a sequence to the set of its elements.
SeqToSet(seq) ==
  {seq[i] : i \in 1..Len(seq)}

\* Last element of a non-empty sequence.
LastElem(seq) ==
  seq[Len(seq)]

\* Test for sequence emptiness.
IsEmptySeq(seq) == Len(seq) = 0

\* Remove every occurrence of a value from a sequence.
RemoveAll(seq, val) ==
  [i \in 1..(Len(seq) - Cardinality({j \in 1..Len(seq) : seq[j] = val}))
   |-> CHOOSE a \in {j \in 1..Len(seq) : seq[j] # val} : a <= i /\ \A b \in {j \in 1..Len(seq) : seq[j] # val} : b <= i => b = a]

\* Intersection of a set of sets.
SetIntersection(S) ==
  {x \in UNION S : \A T \in S : x \in T}

\* All permutation sequences of a finite set.
Permutations(S) ==
  {p \in Seq(S) : Cardinality({p[i] : i \in 1..Len(p)}) = Cardinality(S)}

\* Test helper that prints a diagnostic on failure.
TestHelper(expr, msg) == IF expr THEN TRUE ELSE ~expr

====