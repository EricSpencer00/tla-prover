---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS MaxVals, MaxElems

\* Test if two sets intersect (have any common element).
Intersects(s, t) == \E x \in s : x \in t

\* Maximum/minimum over a nonempty set of natural numbers.
MaxVal(s) == CHOOSE x \in s :
  \A y \in s : y <= x
MinVal(s) == CHOOSE x \in s :
  \A y \in s : y >= x

\* Generalized reduction (fold) over a set: combine elements with an
\* accumulator function, starting from init.
SetReduce(f, init, s) ==
  LET g[T \in SUBSET s] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == g[T \ {x}]
             IN f[x, rest]
  IN g[s]

\* Sequence reduction using the same combine-accumulator style; the
\* underlying folding is delegated to the Sequences library.
SeqReduce(f, init, seq) ==
  SELECT x \in seq : TRUE
    => f[x, SeqReduce(f, init, Tail(seq))]
  : init

\* Find the index of an element in a sequence; 0 means "not found".
IndexOf(seq, x) ==
  CHOOSE k \in 1..Len(seq) : seq[k] = x
    OTHERWISE 0

\* Convert a sequence to the set of its elements.
SeqToSet(seq) ==
  { seq[k] : k \in 1..Len(seq) }

\* The last element of a nonempty sequence.
Last(seq) == seq[Len(seq)]

\* Empty-sequence test.
IsEmpty(seq) == Len(seq) = 0

\* Remove all instances of a value from a sequence.
RemoveAll(seq, x) ==
  SELECT y \in [1..Len(seq)] -> MaxVals : \A k \in 1..Len(seq) : (k \in { i : y[i] = x } <=> FALSE)

\* Intersection of a family of sets.
SetFamilyIntersect(family) ==
  { x \in MaxVals : \A s \in family : x \in s }

\* All permutations of a set of numbers.
PermutationsOf(s) ==
  { p \in [1..Cardinality(s) -> MaxVals] :
      { p[k] : k \in 1..Cardinality(s) } = s }

\* Test helper that prints a message (value of x) before asserting p; in
\* TLC the Print statement triggers a runtime diagnostic, not a property.
AssertWithMessage(p, x) ==
  Print("Asserting ", x) /\ p

\* Additional symbols required by the reference .cfg: invariants, properties,
\* and the usual spec/initial/next framing, though this module has no state.
NoState == TRUE
Spec == NoState
Init == NoState
Next == NoState
StateConstraint == NoState
SpecAccepted == Spec /\ Init /\ Next /\ StateConstraint
====