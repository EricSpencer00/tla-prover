---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
Seqs == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, p, candidate, cnt

TypeOK ==
  /\ seq \in Seqs
  /\ p \in Nat
  /\ candidate \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in Seqs
  /\ p = 1
  /\ candidate \in Values
  /\ cnt = 0

Scan ==
  /\ p <= Len(seq)
  /\ (IF cnt = 0 THEN candidate' = seq[p] /\ cnt' = 1
      ELSE IF seq[p] = candidate THEN cnt' = cnt + 1
      ELSE cnt' = cnt - 1)
  /\ p' = p + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Scan]_<<seq, p, candidate, cnt>>

Correct ==
  (Len(seq) > 0 /\ \A i \in 1 .. Len(seq) : seq[i] # candidate) \/ (p > Len(seq) /\ candidate = seq[1])
  \/ (p > Len(seq) /\ \A i \in 1 .. Len(seq) : \A j \in 1 .. Len(seq) : seq[i] # seq[j]))

Inv ==
  /\ Len(seq) <= bound
  /\ (p > Len(seq) => cnt = 0 \/ cnt = 1)

====