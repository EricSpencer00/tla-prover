---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

ASSUME Values \subseteq \Z

\* The full partition operation is abstracted away: given an interval and a pivot,
\* the model may pick any resulting sequence that a real Quicksort partition could
\* produce -- it must preserve elements outside the interval and must place all
\* elements at/below the pivot index no greater than all elements above it.
Partitioned(se, i, j, s, p) ==
  /\ \A k \in DOMAIN s : (k \notin i..j) => s[k] = se[k]
  /\ \A x \in i..j : \A y \in (j+1)..(p-1) : s[x] <= s[y]
  /\ \A x \in i..j : \A y \in p..Len(se) : s[x] <= s[y]

\* Automorphisms of a domain are bijections from that domain to itself. Permutations
\* of a sequence are its compositions with any such bijection; the image as a bag
\* therefore counts each value exactly as often as the original did.
DomainPermutation(d, s) == {Compose(f, s) : f \in [d -> d]}
Automorphism(d) == {f \in [d -> d] : f \in FINITE /\ f \in INJECTIVE}
Permutation(d, s) == {Compose(f, s) : f \in Automorphism(d)}
Bag(s) == [c \in Values |-> Cardinality({i \in DOMAIN s : s[i] = c})]

\* This is a copy of Seq from the standard module, but finite (bounded in length)
\* rather than potentially infinite -- the model must stay finite in every state.
LimitedSeq(d) == CHOOSE s \in [1..d -> Values] : TRUE

VARIABLES seq, original, todo, pc
vars == <<seq, original, todo, pc>>

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ original \in [1..MaxSeqLen -> Values]
  /\ todo \subseteq (1..MaxSeqLen)
  /\ pc \in {"main", "done"}

Init ==
  /\ seq = LimitedSeq(MaxSeqLen)
  /\ original = seq
  /\ todo = {1..MaxSeqLen}
  /\ pc = "main"

\* The work set is a set of intervals, represented by their lower endpoints; the
\* interval a..b is implicitly b = NextIn(todo, a). Subdividing an interval replaces
\* it with the two halves.
NextIn(S, x) ==
  LET Y == {y \in S : y > x}
  IN IF Y = {} THEN MaxSeqLen ELSE CHOOSE y \in Y : \A z \in Y : y <= z

Partition(i, j) ==
  \E p \in (j+1)..MaxSeqLen, s \in [1..MaxSeqLen -> Values] :
    /\ Partitioned(seq, i, j, s, p)
    /\ seq' = s
  /\ todo' = (todo \ {i}) \cup {i, NextIn(todo, i)}
  /\ UNCHANGED <<original, pc>>

Step ==
  \/ \E i \in todo :
       /\ Len(todo) > 0
       /\ IF i = MaxSeqLen THEN UNCHANGED vars
          ELSE IF NextIn(todo, i) = i + 1 THEN todo' = todo \ {i} /\ UNCHANGED <<seq, original, pc>>
               ELSE Partition(i, NextIn(todo, i))
  \/ pc = "done" /\ UNCHANGED vars

Next ==
  /\ Step
  /\ pc' = (IF Len(todo) = 0 THEN "done" ELSE pc)

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The algorithm finishes with exactly the original elements, now sorted.
PCorrect ==
  (pc = "done") =>
    /\ Permutation(1..MaxSeqLen, seq, original)
    /\ \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i+1]

\* The intervals in the work set form a partition of the domain; the sequence is
\* always a permutation of the original; and any interval still in the set is
\* already sorted relative to every interval that is strictly to its right.
Inv ==
  /\ \A i \in todo, j \in todo : (i <= j) => (NextIn(todo, i) <= NextIn(todo, j))
  /\ Permutation(1..MaxSeqLen, seq, original)
  /\ \A i \in todo : \A k \in i..NextIn(todo, i), l \in (NextIn(todo, i)+1)..MaxSeqLen : seq[k] <= seq[l]

Termination ==
  (pc = "done") ~> (pc = "done")

====