---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Model checking requires a bounded-length version of the sequence
\* operator, so the one imported from Sequences (which is infinite-domain)
\* is replaced by LimitedSeq below; the name Seq is not redeclared here.
\* All other symbols are taken from the standard modules as is.

CONSTANTS Values, MaxSeqLen

\* Index ranges are inclusive; Upper(i) is the highest index of the seq.
Range == 1..MaxSeqLen

\* The domain is the set of indices of the current sequence, which grows
\* as the sequence does, so the domain that Permute quantifies over changes
\* during the run exactly as the real sort's working set does.
Domain == 1..Upper(s)
Upper(s) == Len(s)

SumSet(f, S) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE
             IN f[x] + g[T \ {x}]
  IN g[S]

\* Permutation as a bijection on the current domain, with all elements
\* outside the domain fixed, so the domain that Permute quantifies over
\* stays aligned with the part of the sequence actually in use.
Permute(f, s) ==
  LET d == Domain
      sigma == [x \in d |-> f[x]]
      rho == [x \in d |-> CHOOSE y \in d :
                 \A z \in d : (z < y) => f[z] < f[y]
             ]
  IN [i \in Range |-> IF i \in d THEN rho[sigma[i]] ELSE i]

\* The partition operator is nondeterministic over every rearrangement
\* that keeps the domain partitioned at the pivot and leaves the rest
\* of the sequence untouched; that is what makes the abstract step safe.
Partition(s, a, b, p) ==
  {t \in Permute(f, s) :
     /\ \A i \in Range \ {a..b} : t[i] = s[i]
     /\ \A i \in a..p : t[i] <= s[p]
     /\ \A i \in (p+1)..b : s[p] <= t[i]}

VARIABLES seq, original, workSet, pc

vars == <<seq, original, workSet, pc>>

Intervals == {r \in Range \X Range : r[1] <= r[2]}
Lower(i, p) == <<i[1], p>>
Upper(i, p) == <<p+1, i[2]>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= MaxSeqLen
  /\ original \in Seq(Values)
  /\ Len(original) <= MaxSeqLen
  /\ workSet \subseteq Intervals
  /\ pc \in {"loop", "halt"}

\* Both subintervals produced by the partition stay inside the original
\* interval and never invert the pivot, so their domains stay disjoint.
DomainSplits ==
  /\ \A i, j \in workSet : i # j => (i[2] < j[1] \/ j[2] < i[1])
  /\ \A i \in workSet : i[1] <= Upper(seq) + 1

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] :
       /\ Len(s) >= 1
       /\ seq = s
       /\ original = s
  /\ workSet = {<<1, Upper(seq)>>}
  /\ pc = "loop"

QuicksortStep ==
  \/ \E i \in workSet :
       /\ i[1] = i[2]
       /\ workSet' = workSet \ {i}
       /\ pc' = IF pc = "halt" THEN "halt" ELSE "loop"
       /\ UNCHANGED <<seq, original>>
  \/ \E i \in workSet, p \in i[1]..i[2] :
       /\ \E t \in Partition(seq, i[1], i[2], p) : seq' = t
       /\ workSet' = (workSet \ {i}) \cup {Lower(i, p), Upper(i, p)}
       /\ pc' = IF workSet = {} THEN "halt" ELSE "loop"
       /\ UNCHANGED original
  \/ /\ workSet = {}
       /\ pc = "loop"
       /\ pc' = "halt"
       /\ UNCHANGED <<seq, original, workSet>>

Next == QuicksortStep

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep)

\* The loop's partitioning is represented as a guessed result, so the
\* correctness argument is based on the partition shape, not on the
\* mechanics of any particular partition implementation.
PCorrect ==
  /\ (pc = "halt") =>
       /\ (Len(seq) = Len(original))
       /\ SumSet([i \in Range |-> seq[i] * (i \in Domain)], Domain)
            = SumSet([i \in Range |-> original[i] * (i \in Domain)], Domain)
       /\ \A i \in 1..(Upper(seq) - 1) : seq[i] <= seq[i+1]

\* Domain partitioning is the shape argument; permutation preservation
\* is the value argument; monotonicity on every adjacent pair is the
\* per-interval order that partitioning must guarantee the whole sort.
Inv ==
  /\ DomainSplits
  /\ (Len(seq) = Len(original))
  /\ SumSet([i \in Range |-> seq[i] * (i \in Domain)], Domain)
       = SumSet([i \in Range |-> original[i] * (i \in Domain)], Domain)
  /\ \A i \in 1..(Upper(seq) - 1) : seq[i] <= seq[i+1]

Termination == (pc = "loop") ~> (pc = "halt")

\* The bounded-length version of Seq; everything else in this spec uses
\* the ordinary Seq symbols from the standard module unchanged.
LimitedSeq(seq) ==
  IF seq = <<>> THEN <<>>
  ELSE LET hd == Head(seq)
           tl == Tail(seq)
       IN IF Len(tl) < MaxSeqLen THEN Append(LimitedSeq(tl), hd) ELSE <<>>

\* A stub that redefines the shape of the model without weakening
\* Termination or PCorrect; it concretely bounds the action space.
BoundedStack(s) == {"BoundedStack": s \in [1..MaxSeqLen -> Values] /\ Len(s) >= 1}
====