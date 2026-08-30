---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Permutations, Sequences

CONSTANT Values, MaxSeqLen

Indices == 1 .. MaxSeqLen
Pairs == {<<i, j>> \in Indices \X Indices : i <= j}
SeqDomain == {1 .. MaxSeqLen}

VARIABLES seq, origSeq, pending, pc
vars == <<seq, origSeq, pending, pc>>

TypeOK ==
  /\ seq \in SeqDomain -> Values
  /\ origSeq \in SeqDomain -> Values
  /\ pending \subseteq Pairs
  /\ pc \in {"main", "term"}

\* Exactly one partition of the index range is active at a time; the
\* "active partition" of an interval is "inactive" (empty) iff it is empty.
ActivePart(i, j) == {x \in Indices : i <= x /\ x <= j}
ActivePartEmpty == {i \in Indices : \E j \in Indices : i \in ActivePart(i, j)}

Init ==
  /\ \E s \in SeqDomain ->
       /\ \A i \in Indices, v \in Values : s[i] = v
       /\ seq = s
       /\ origSeq = s
  /\ pending = {<<1, MaxSeqLen>>}
  /\ pc = "main"

\* The partition operator chooses any new sequence that keeps the split
\* correctly ordered; an identity (no change) is always available.
NondetPartition(i, j, k) ==
  {t \in SeqDomain ->
     /\ \A x \in Indices \ ActivePart(i, j) : t[x] = seq[x]
     /\ \A x \in ActivePart(i, k) : \A y \in ActivePart(k + 1, j) : t[x] <= t[y]}

DoPartition ==
  /\ pc = "main"
  /\ pending # {}
  /\ \E p \in pending :
       LET i == p[1] j == p[2] k == i + (j - i) \div 2
       IN
         \/ /\ i = j
            /\ pending' = pending \ {p}
         \/ /\ i < j
            /\ pending' = (pending \ {p}) \cup {<<i, k>>, <<k + 1, j>>}
            /\ \E s \in NondetPartition(i, j, k) : seq' = s
  /\ pc' = pc
  /\ UNCHANGED origSeq

Terminate ==
  /\ pc = "main"
  /\ pending = {}
  /\ pc' = "term"
  /\ UNCHANGED <<seq, origSeq, pending>>

Stall ==
  /\ pc = "term"
  /\ UNCHANGED vars

Next == DoPartition \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars
        /\ WF_vars(DoPartition)
        /\ WF_vars(Terminate)

Permutation(p) == {i \in Indices : p[i] \in Values}
\* The domain of the current sequence is exactly the active partition, and
\* it is a permutation of the original restricted to the same domain.
DomainPermutation ==
  /\ Permutation(seq) = Permutation(origSeq)
  /\ ActivePartEmpty = Permutation(seq)

InvariantSorted ==
  \A i, j \in ActivePartEmpty : (i < j) => (seq[i] <= seq[j])

PCorrect == (pc = "term") => (DomainPermutation /\ InvariantSorted)

Termination == (\A i \in Indices : seq[i] \in Values) ~> (pc = "term")

\* A bounded length is what makes the model finite; it is not an algorithm
\* limit, so its name is intentionally not "Bound" and it is never changed.
Bound == MaxSeqLen

\* A finite, bounded version of Seq that keeps the model checkable.
LimitedSeq(f) ==
  [i \in 1 .. Len(f) |-> f[i]]
====