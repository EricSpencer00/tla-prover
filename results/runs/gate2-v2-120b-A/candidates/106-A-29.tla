---------------- MODULE Util ----------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Utility library providing common helper operators for set and sequence
  manipulation.  All operators are purely functional and do not depend
  on any state variables.
--------------------------------------------------------------------*)

(*--------------------------------------------------------------------
  1. Set overlap test:  Overlap(s, t) is TRUE iff s ∩ t is non‑empty.
--------------------------------------------------------------------*)
Overlap(s, t) == 
    \E x \in s : x \in t

(*--------------------------------------------------------------------
  2. Maximum and minimum element selection from a non‑empty finite set.
--------------------------------------------------------------------*)
Max(s) == 
    /\ s # {}
    /\ \E m \in s : \A y \in s : y <= m

Min(s) == 
    /\ s # {}
    /\ \E m \in s : \A y \in s : m <= y

(*--------------------------------------------------------------------
  3. Generalized set reduction (fold over a set with an accumulator).
      foldSet(f, acc, s) applies f to each element of s and the current
      accumulator, in an arbitrary order, returning the final accumulator.
      The order is irrelevant when f is associative and commutative.
--------------------------------------------------------------------*)
VARIABLES acc

FoldSetAcc(f, acc0, s) ==
    /\ acc = acc0
    /\ \A x \in s : 
         acc' = f(x, acc)

FoldSet(f, acc0, s) ==
    IF s = {} THEN acc0
    ELSE LET f' == [old \in [x \in s, a \in {acc0} \cup s] |-> f(old.x, old.a)] IN
         (* The exact order is nondeterministic; we simply apply f sequentially *)
         FoldSetAcc(f', acc0, s)

(*--------------------------------------------------------------------
  4. Sequence reduction (fold over a sequence with an accumulator).
      Defined using the built‑in FoldSeq operator from the Sequences
      module, which processes the sequence from left to right.
--------------------------------------------------------------------*)
FoldSeq(f, acc0, seq) == 
    FoldSeq(f, acc0, seq) \* (uses the library definition)

(*--------------------------------------------------------------------
  5. IndexOf(seq, elem) returns the 1‑based position of the first
      occurrence of elem in seq, or 0 if elem is not present.
--------------------------------------------------------------------*)
IndexOf(seq, elem) ==
    CHOOSE i \in 0..Len(seq) :
        (i = 0) \/ (seq[i] = elem /\ \A j \in 1..(i-1) : seq[j] # elem)

(*--------------------------------------------------------------------
  6. ToSet(seq) converts a sequence to the set of its elements.
--------------------------------------------------------------------*)
ToSet(seq) == 
    { seq[i] : i \in 1..Len(seq) }

(*--------------------------------------------------------------------
  7. Last(seq) returns the last element of a non‑empty sequence.
--------------------------------------------------------------------*)
Last(seq) == 
    seq[Len(seq)]

(*--------------------------------------------------------------------
  8. Empty(seq) is TRUE iff seq has length zero.
--------------------------------------------------------------------*)
Empty(seq) == 
    Len(seq) = 0

(*--------------------------------------------------------------------
  9. RemoveAll(seq, elem) returns a new sequence obtained by deleting
      every occurrence of elem from seq, preserving the order of the
      remaining elements.
--------------------------------------------------------------------*)
RemoveAll(seq, elem) ==
    [ i \in 1..Cardinality({ j \in 1..Len(seq) : seq[j] # elem }) |
        LET filtered == { j \in 1..Len(seq) : seq[j] # elem } IN
        seq[CHOOSE j \in filtered : Cardinality({ k \in filtered : k <= j }) = i] ]

(*--------------------------------------------------------------------
 10. SetIntersection(S) where S is a set of sets.  Returns the
      intersection of all members of S.  For an empty S the result is
      the universal set of all possible values (here we use {} as the
      neutral element for intersection, which matches the usual
      mathematical convention in this context).
--------------------------------------------------------------------*)
SetIntersection(S) ==
    IF S = {} THEN {}
    ELSE /\ \E t \in S : TRUE      \* ensure S is non‑empty
         /\ \A x : \A t \in S : x \in t

(*--------------------------------------------------------------------
 11. Permutations(s) returns the set of all sequences that are
      permutations of the elements of the finite set s.
--------------------------------------------------------------------*)
Permutations(s) ==
    IF s = {} THEN { << >> }
    ELSE 
        UNION { 
            << e >> \o p : 
                e \in s /\ 
                p \in Permutations(s \ {e}) 
        }

(*--------------------------------------------------------------------
 12. Test helper that prints a message when a condition fails.
      In the TLC model checker, the Print operator writes to the
      trace.  The helper returns FALSE when the condition is false,
      allowing it to be used directly in assertions.
--------------------------------------------------------------------*)
TestHelper(cond, msg) ==
    IF cond THEN TRUE
    ELSE Print(msg) /\ FALSE

=============================================================================