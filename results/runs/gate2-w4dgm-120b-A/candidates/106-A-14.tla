---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS InitSet

SetSpec == {"x", "y", "z"}

Spec == "Spec"

VARIABLES dict, control

vars == <<dict, control>>

\* SetIntersection: true iff two value sets overlap (used by conflict checks).
SetIntersection(A, B) == BOOLEAN(A \cap B)

\* SetMax / SetMin: pick an arbitrary max/min element from a non-empty set.
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : y >= x

\* SetReduce: generic accumulation over a set (commutative accumulator).
SetReduce(f, S, a) ==
  IF S = {} THEN a
  ELSE LET x == CHOOSE y \in S : TRUE IN f(a, x, SetReduce(f, S \ {x}, a))

\* SeqReduce: generic accumulation over a sequence via a library fold.
SeqReduce(f, seq, a) == FoldSeq(f, seq, a)

\* SeqFind: index of pattern in a sequence, -1 if not found.
SeqFind(seq, pat) ==
  LET n == Len(seq) IN
  LET m == Len(pat) IN
  LET Search(i) ==
    IF i > n - m + 1 THEN -1
    ELSE IF \A k \in 1..m : seq[i + k - 1] = pat[k] THEN i
    ELSE Search(i + 1)
  IN Search(1)

SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Permutations: all ordering arrangements of a finite set's elements.
Permutations(S) ==
  LET L == Cardinality(S) IN
  LET AddTo(seq, x) == [i \in 1..(Len(seq) + 1) |-> IF i <= Len(seq) THEN seq[i] ELSE x] IN
  LET Build(k) ==
    IF k = 1 THEN { <<x>> : x \in S }
    ELSE UNION { { AddTo(seq, x) : seq \in Build(k - 1) } : x \in S }
  IN Build(L)

Last(seq) == IF seq = <<>> THEN "empty" ELSE seq[Len(seq)]

SeqEmpty(seq) == seq = <<>>

SeqWithout(seq, e) == SelectSeq(seq, LAMBDA x : x # e)

\* IntersectAll: common-values across a set of sets.
IntersectAll(S) == CHOOSE x \in {y \in SetSpec : \A A \in S : y \in A} : TRUE

\* Assert: test helper that prints a message on failure (no-op if true).
Assert(cond, msg) == IF cond THEN TRUE ELSE ~cond /\ msg

TypeOK == /\ dict \in [Spec -> SUBSET SetSpec]
          /\ control \in 0..1

Spec == /\ dict = [s \in Spec |-> InitSet]
        /\ control \in {0, 1}

\* RotateControl: the shared-control variable cycles 0, 1, 0, 1...
RotateControl == /\ control' = 1 - control
                 /\ UNCHANGED dict

\* ResetDict: when control is 0, return the shared record to its initial set.
ResetDict == /\ control = 0
             /\ dict' = [s \in Spec |-> InitSet]
             /\ UNCHANGED control

\* RotateLeft: when control is 1, rotate a fixed element from one set to another.
RotateLeft == /\ control = 1
              /\ \E a, b \in Spec :
                   /\ a # b
                   /\ dict[a] # {}
                   /\ dict' = [dict EXCEPT ![a] = dict[a] \ {"x"}, ![b] = dict[b] \cup {"x"}]
              /\ UNCHANGED control

Next == RotateControl \/ ResetDict \/ RotateLeft

\* Every element eventually returns to its original set (recoverable after rotation).
Recovery == \A s \in Spec : (dict[s] # InitSet) ~> (dict[s] = InitSet)

\* The two disjoint-control regimes keep the shared record conflict-free.
ControlSeparation == control # 1

====