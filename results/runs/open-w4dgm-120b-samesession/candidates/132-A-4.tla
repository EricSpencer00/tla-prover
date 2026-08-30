---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

Seqs == { f \in [1..n -> Values] : n \in 0..bound }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ count \in 0..bound

Init ==
  /\ \E s \in Seqs :
       /\ seq = s
       /\ pos = 1
  /\ \E x \in Values :
       cand = x
  /\ count = 0

Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF count = 0 THEN cand' = x /\ count' = 1
       ELSE IF x = cand THEN count' = count + 1 /\ cand' = cand
       ELSE count' = count - 1 /\ cand' = cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Correct ==
  /\ \A i \in 1..Len(seq) : seq[i] \in Values
  /\ \A x \in Values :
       (\A i \in 1..Len(seq) : seq[i] = x) => cand = x

Inv ==
  \A i \in 1..bound :
    /\ i >= Len(seq)
    /\ (i = bound => i = Len(seq))
    /\ (i > 0 => pos <= i + 1)

BoundedSeq == Sequences.Seq

====