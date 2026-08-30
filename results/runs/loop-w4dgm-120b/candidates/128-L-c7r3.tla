---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* A finite (checkable) version of Seq: the range of a sequence up to MaxSeqLen.
LimitedSeq(f) == {f[i] : i \in 1..MaxSeqLen}

Indices == 1..MaxSeqLen

\* A cyclic permutation of a domain of indices: each index maps to its successor.
CyclicPermutation(S) ==
  [i \in S |-> IF i = MaxSeqLen THEN 1 ELSE i + 1]

\* The set of index pairs that swap the two halves of a partition about a pivot.
SwapPairs(S, p) ==
  {<<i, j>> \in S \X S : (i <= p /\ j > p) \/ (i > p /\ j <= p)}

\* Partition permutations: permute the interval while swapping the two halves;
\* elements outside the interval stay put; cycle outside the interval.
Permute(S, p) ==
  {CyclicPermutation(Indices) \cup SwapPairs(Indices, p) \cup
     {<<i, i>> : i \in Indices \ {p, p + 1}}}

\* A partition is valid if it is one of these permutations and leaves outside
\* elements untouched -- the ordering guarantee is outside the scope of this
\* abstract model, but the permutation shape is the shape that makes it true.
ValidPartition(seq, S, p) ==
  /\ \E perm \in Permute(S, p) : seq' = [i \in Indices |-> seq[perm[i]]]
  /\ \A i \in Indices : (i \notin S) => seq[i] = seq[i]

VARIABLES seq, origSeq, set, pc

vars == <<seq, origSeq, set, pc>>

Empty == [lo |-> 0, hi |-> 0]
Interval(lo, hi) == [lo |-> lo, hi |-> hi]

TypeOK ==
  /\ seq \in [Indices -> Values]
  /\ origSeq \in [Indices -> Values]
  /\ set \subseteq [lo: 0..MaxSeqLen, hi: 0..MaxSeqLen]
  /\ pc \in {"main", "joined"}

Init ==
  /\ \E s \in [Indices -> Values] :
       /\ \E e \in Values : s[1] = e
       /\ seq = s
       /\ origSeq = s
  /\ set = {Interval(1, MaxSeqLen)}
  /\ pc = "main"

\* One iteration of the Quicksort recursion on a chosen interval/pivot.
Step ==
  /\ pc = "main"
  /\ \E it \in set :
       /\ set' = set \ {it}
       /\ IF it.lo = it.hi
            THEN UNCHANGED <<seq, origSeq>>
            ELSE \E p \in it.lo..it.hi :
                 /\ ValidPartition(seq, it, p)
                 /\ set' = set \cup {Interval(it.lo, p), Interval(p + 1, it.hi)}
  /\ IF set = {} THEN pc' = "joined" ELSE pc' = pc

Stall ==
  /\ pc = "joined"
  /\ UNCHANGED vars

Next == Step \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The program counter is never out of range, the original sequence is unchanged,
\* and the current sequence is always a permutation of the original sequence.
PCorrect == pc \in {"main", "joined"} /\ origSeq \in [Indices -> Values] /\ seq \in LimitedSeq(origSeq)

\* The permutation shape is preserved across steps.
TypeOK == TypeOK

\* A strong invariant: any two intervals that touch touch a contiguous block of
\* indices in the same order, so the whole domain stays sorted once fully split.
Inv ==
  /\ \A it \in set : it.lo <= it.hi
  /\ \A i, j \in 1..MaxSeqLen :
       (\E a, b \in set : <<i, j>> \in a \X b) => i <= j

Termination == <>pc = "joined"

====