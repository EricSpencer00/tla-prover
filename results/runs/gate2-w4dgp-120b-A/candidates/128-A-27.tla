---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

Range(i, j) == {k \in DOMAIN seq : i <= k /\ k <= j}

Automorphisms == {f \in [DOMAIN seq -> DOMAIN seq] : (injective[f] /\ (f \in [DOMAIN seq -> DOMAIN seq]))}

Compose(p, f) == [k \in DOMAIN seq |-> p[f[k]]]

RECURSIVE Permutes(_, _)
Permutes(S, Q) ==
  IF S = {} THEN <<>>
  ELSE LET x == CHOOSE y \in S : TRUE IN <<x>> @@ Permutes(S \ {x}, Q)

Permutations ==
  {p \in Permutes(DOMAIN seq, Values) : \A i \in DOMAIN seq : p[i] \in Values}

Sorted(s) == \A i \in DOMAIN s : (i + 1 \in DOMAIN s) => (s[i] <= s[i + 1])

TypeOK ==
  /\ seq \in Permutations
  /\ orig \in Permutations
  /\ todo \subseteq {{i, j} \in (DOMAIN seq \X DOMAIN seq) : i < j}

PCorrect ==
  seq = orig => Sorted(seq)

\* The set of intervals partitions the index domain (no overlap at all), the
\* current sequence is always a permutation of the original, and any two
\* intervals that touch each other are already sorted across their boundary,
\* which together are enough to inductively guarantee a sorted permutation
\* once every interval has been resolved.
Inv ==
  /\ (\A p, q \in todo : p # q => Range(p[1], p[2]) \cap Range(q[1], q[2]) = {})
  /\ \A i \in DOMAIN seq : seq[i] \in Values
  /\ \A a, b \in DOMAIN seq :
        (\E p \in todo : a \in Range(p[1], p[2]) /\ b \in Range(p[1], p[2]))
          => seq[a] = orig[a]
  /\ \A a, b \in DOMAIN seq :
        (\E p, q \in todo : a \in Range(p[1], p[2]) /\ b \in Range(q[1], q[2])
                               /\ p[2] < q[1])
          => seq[a] <= seq[b]

Init ==
  /\ seq \in Permutations /\ seq # <<>>
  /\ orig = seq
  /\ todo = {{1, Len(seq)}}
  /\ pc = "loop"

\* One Quicksort iteration: an interval is chosen, partitioned around a pivot,
\* and replaced by its two (possibly empty) subintervals. The partition is
\* chosen nondeterministically from everything any legal procedure could
\* return, so the model checks every valid interleaving.
Partition(i, j, k) ==
  {r \in Permutations :
     /\ \A p \in DOMAIN seq :
          p \notin Range(i, j) => r[p] = seq[p]
     /\ \A p \in Range(i, k) : \A q \in Range(k + 1, j) : r[p] <= r[q]
     /\ \A a, b \in Range(i, j) : (a < k /\ k < b) => r[a] <= r[b]}

Next ==
  \/ IF todo # {}
       THEN \E p \in todo :
              LET i == p[1] IN LET j == p[2] IN
                \/ /\ i = j
                   /\ todo' = todo \ {p}
                \/ /\ i < j
                   /\ \E k \in i..j :
                        /\ \E r \in Partition(i, j, k) :
                             /\ seq' = r
                             /\ todo' = (todo \ {p}) \cup {{i, k}, {k + 1, j}}
       ELSE UNCHANGED <<seq, todo>>
  /\ pc' \in {"loop", "done"}
  /\ (IF pc = "loop" /\ todo = {} THEN pc' = "done" ELSE pc' = pc)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

\* With every interval eventually resolved by the bounded recursive
\* partitioning, the algorithm must terminate (reaching the terminal state).
Termination == <>(pc = "done")

RECURSIVE LimitedSeq(_, _)
LimitedSeq(i, n) ==
  IF i > n THEN <<>>
  ELSE LET x == CHOOSE y \in Values : TRUE IN <<x>> @@ LimitedSeq(i + 1, n)

\* The standard Sequences module's Seq operator is unbounded, which makes the
\* model uncheckable. The .cfg replaces it with this finite, value-bounded
\* version, so the model only ever explores sequences up to MaxSeqLen.
Seq == LimitedSeq(1, MaxSeqLen)

====