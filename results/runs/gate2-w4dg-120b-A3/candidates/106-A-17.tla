---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  TRUE

CONSTANTS
  NumberOfPermutations
  Elements
  DefaultValue

\* The module has no actors or state – the following are pure helper operators.
\* Nothing below updates system state; every operator takes its inputs as
\* arguments and returns a value.  They are intentionally pure because they
\* are meant to be imported by other spec modules without side effects.
\* The reference config makes no use of the module's SPECIFICATION, INIT,
\* NEXT, INVARIANTS, or PROPERTIES, but the identifiers must still exist.

\* 1. Set intersection test: overlap iff the two sets share an element.
Intersect(a, b) ==
  \/ \E e \in a : e \in b
  \/ \E e \in b : e \in a

\* 2. The max (or min) element of a non-empty set.
Max(s) ==
  LET mx == CHOOSE x \in s :
                \A y \in s : y <= x
  IN mx
Min(s) ==
  LET mn == CHOOSE x \in s :
                \A y \in s : y >= x
  IN mn

\* 3. Generalized set reduction (fold) using an accumulator of arbitrary type.
Reduce(f, s, init) ==
  LET add(x) == [m \in {init} \cup {f[i] : i \in s} |-> IF x = init THEN f[x] ELSE m]
  IN { add[x] : x \in s }

\* 4. Sequence reduction (fold) using the library's FoldSeq operator.
SeqReduce(f, seq, init) ==
  LET g == [x \in {1 .. Len(seq)} |-> f[seq[x]]]
  IN FoldSeq(g, init)

\* 5. Index of an element in a sequence (or 0 if not present).
IndexOf(seq, e) ==
  IF e \in Range(seq) THEN
    CHOOSE k \in 1 .. Len(seq) : seq[k] = e
  ELSE 0

\* 6. Convert a sequence into the set of its elements.
SetOf(seq) ==
  { seq[i] : i \in 1 .. Len(seq) }

\* 7. The last element of a sequence.
Last(seq) ==
  seq[Len(seq)]

\* 8. Test a sequence for emptiness.
Empty(seq) ==
  Len(seq) = 0

\* 9. Remove all occurrences of a value from a sequence.
Remove(seq, v) ==
  SelectSeq(seq, LAMBDA x : x # v)

\* 10. Intersection of a set of sets.
SetIntersection(ss) ==
  IF ss = {} THEN {}
  ELSE { x \in CHOOSE s \in ss : TRUE : \A t \in ss : x \in t }

\* 11. All permutation sequences of a finite set (numbered by an index).
Permutations ==
  { seq \in [1 .. NumberOfPermutations -> Elements] : \A i \in 1 .. NumberOfPermutations : seq[i] # DefaultValue }

\* 12. A test helper: prints diagnostic info on a false condition.
TestHelper(expr) ==
  IF expr THEN TRUE ELSE Print("Test failure: ", expr) = 0

\* The module's SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES must
\* exist, even though they are never invoked -- the .cfg expects them.
\* Their bodies are deliberately idle.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====