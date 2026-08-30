---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Seqs == UNION { [1 .. n -> {A, B, C}] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in {A, B, C}
  /\ cnt \in Nat

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

ScanStep ==
  /\ pos <= Len(seq)
  /\ \/ /\ seq[pos] = cand
        /\ cnt' = cnt + 1
        /\ cand' = cand
     \/ /\ cnt = 0
        /\ cnt' = 1
        /\ cand' = seq[pos]
     \/ /\ seq[pos] # cand
        /\ cnt > 0
        /\ cnt' = cnt - 1
        /\ cand' = cand
  /\ pos' = pos + 1
  /\ seq' = seq

Spec == Init /\ [][ScanStep]_vars /\ WF_vars(ScanStep)

Correct ==
  \A i \in 1 .. Len(seq) : (\A j \in 1 .. Len(seq) : seq[j] = seq[i]) => seq[i] = cand

Inv == \A i \in 1 .. Len(seq) : (\A j \in 1 .. Len(seq) : seq[j] = seq[i])
  => (i >= pos \/ seq[i] = cand)

BoundedSeq == UNION { [1 .. n -> {A, B, C}] : n \in 0 .. bound }

====