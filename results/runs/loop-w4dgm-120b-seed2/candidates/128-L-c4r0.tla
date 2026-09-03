---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* Finite version of the sequence operator; Seq from Sequences is replaced by this
LimitedSeq(f, n) == [i \in 1..n |-> f[i]]

Intervals == {i \in 1..MaxSeqLen : <<1, i>>}
Permutations == {g \in [1..MaxSeqLen -> 1..MaxSeqLen] : \A x \in 1..MaxSeqLen : g[x] \in 1..MaxSeqLen /\ \A x \in 1..MaxSeqLen : \A y \in 1..MaxSeqLen : g[x] = g[y] => x = y}
Partitions(s, lo, hi, piv) == {t \in [1..MaxSeqLen -> Values] :
  /\ (hi < MaxSeqLen => \A i \in (hi + 1)..MaxSeqLen : t[i] = s[i])
  /\ \A x \in lo..piv : \A y \in (piv + 1)..hi : t[x] <= t[y]}
Merge(s, lo, piv, hi) == [i \in 1..MaxSeqLen |->
  IF i < lo \/ i > hi
    THEN s[i]
    ELSE IF i <= piv
      THEN s[i]
      ELSE s[i]]

VARIABLES seq, initSeq, todo, pc

vars == <<seq, initSeq, todo, pc>>

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ initSeq \in [1..MaxSeqLen -> Values]
  /\ todo \in SUBSET Intervals
  /\ pc \in {"loop", "done"}

Init ==
  \E s \in [1..MaxSeqLen -> Values] :
    /\ seq = s
    /\ initSeq = s
    /\ todo = {<<1, MaxSeqLen>>}
    /\ pc = "loop"

Loop ==
  /\ pc = "loop"
  /\ todo # {}
  /\ \E r \in todo :
       /\ todo' = todo \ {r}
       /\ IF r[1] = r[2]
            THEN todo'
            ELSE \E piv \in r[1]..r[2] :
                   /\ \E t \in Partitions(seq, r[1], r[2], piv) :
                        seq' = t
                   /\ todo' = todo' \cup {<<r[1], piv>>, <<piv + 1, r[2>>}
  /\ pc' = IF (todo \ {r}) = {} /\ seq' = seq THEN "done" ELSE "loop"

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Loop \/ Stall

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Loop)

PCorrect ==
  /\ (pc = "done" => \A i \in 1..MaxSeqLen : \A j \in 1..MaxSeqLen : i < j => seq[i] <= seq[j])
  /\ \E g \in Permutations : initSeq = [i \in 1..MaxSeqLen |-> seq[g[i]]]

Sorted == {s \in [1..MaxSeqLen -> Values] : \A i \in 1..MaxSeqLen : \A j \in 1..MaxSeqLen : i < j => s[i] <= s[j]}
DomainPart == {s \in [1..MaxSeqLen -> Values] : \E c \in 1..MaxSeqLen : \A i, j \in 1..c : s[i] = initSeq[j]}
Permutation == {s \in [1..MaxSeqLen -> Values] : \E g \in Permutations : s = [i \in 1..MaxSeqLen |-> initSeq[g[i]]]}

Inv == DomainPart /\ Permutation /\ \A i \in 1..MaxSeqLen : \A j \in 1..MaxSeqLen : i < j => seq[i] <= seq[j]

Termination == (pc = "loop") ~> (pc = "done")

====