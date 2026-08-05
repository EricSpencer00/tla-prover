---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A sorter interval is a range of positions, interpreted as a set of indices.
Intervals == SUBSET [lo : 1..MaxSeqLen, hi : 1..MaxSeqLen]

\* Permutations are defined by composition with automorphisms of the domain.
Permutation(p) ==
  /\ DOMAIN p = 1..MaxSeqLen
  /\ \A q \in [1..MaxSeqLen -> 1..MaxSeqLen] : (q \in DOMAIN /\ \A i \in DOMAIN : q[i] = i) => p = q

\* A partition of [lo..hi] around a pivot idx is any arrangement that leaves
\* elements outside the interval untouched and keeps the pivot split ordered.
PARTITION(s, lo, hi, idx) ==
  {t \in [1..MaxSeqLen -> Values] :
     /\ \A i \in 1..MaxSeqLen : (i < lo \/ i > hi) => t[i] = s[i]
     /\ \A i \in lo..idx, j \in idx+1..hi : t[i] <= t[j]}

VARIABLES seq, orig, todo, pc
vars == <<seq, orig, todo, pc>>

RECURSIVE domain(_)
domain(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN {x} \cup domain(S \ {x})

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ todo \subseteq Intervals
  /\ pc \in {"Loop", "Done"}

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] : /\ Cardinality({i \in 1..MaxSeqLen : s[i] # 0}) <= MaxSeqLen
                                                /\ seq = s /\ orig = s
  /\ todo = {<<1, MaxSeqLen>>}
  /\ pc = "Loop"

\* One iteration: pick an interval, either discard a singleton or partition it.
LoopStep ==
  \/ \E I \in todo :
       /\ pc = "Loop"
       /\ LET lo == I[1] IN LET hi == I[2] IN
            IF lo = hi
            THEN todo' = todo \ {I}
            ELSE \E idx \in lo..hi :
                 \E t \in PARTITION(seq, lo, hi, idx) :
                   /\ seq' = t
                   /\ todo' = (todo \ {I}) \cup {<<lo, idx>>, <<idx+1, hi>>}
       /\ UNCHANGED <<orig, pc>>
  \/ \E I \in todo :
       /\ todo = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, todo>>

Stall == pc = "Done" /\ UNCHANGED vars

Next == LoopStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(\E I \in Intervals : LoopStep)

\* Permutation, full coverage of the domain, and relative sortedness between
\* intervals (not yet between all positions) constitute the inductive invariant.
Inv ==
  /\ Permutation(seq)
  /\ DOMAIN seq = domain({p.seq : p \in Permutation([1..MaxSeqLen -> 1..MaxSeqLen])})
  /\ \A I, J \in todo : (I[2] < J[1] \/ I[1] > J[2]) => (I[2] < J[1] => seq[I[2]] <= seq[J[1]])

\* When the algorithm has drained its work set it is fully sorted.
PCorrect ==
  (pc = "Done") =>
    /\ seq = orig
    /\ \A i \in 1..MaxSeqLen - 1 : seq[i] <= seq[i+1]

Termination == <>(pc = "Done")
====