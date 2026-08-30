---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

Values == {A, B, C}

\* A bounded version of Seq that keeps the state space finite for model
\* checking: only sequences of length at most the current bound are
\* reachable, though the underlying definition still uses the full Seq.
BoundedSeq == Seq

AllSeqs == UNION { [1..n -> Values] : n \in 0..bound }

VARIABLES seq, pos, candidate, counter

vars == <<seq, pos, candidate, counter>>

Bump(x) == IF x = bound THEN bound ELSE x + 1

TypeOK ==
  /\ seq \in AllSeqs
  /\ pos \in 1..(bound + 1)
  /\ candidate \in Values
  /\ counter \in 0..bound

Init ==
  /\ seq \in AllSeqs
  /\ pos = 1
  /\ candidate \in Values
  /\ counter = 0

\* Boyer-Moore: three cases as the scan advances.
Scan ==
  /\ pos <= Len(seq)
  /\ LET cur == seq[pos] IN
       \/ IF counter = 0 THEN /\ candidate' = cur /\ counter' = 1
                          ELSE IF cur = candidate THEN /\ candidate' = candidate /\ counter' = counter + 1
                          ELSE /\ candidate' = candidate /\ counter' = counter - 1
  /\ pos' = Bump(pos)
  /\ UNCHANGED seq

Spec = Init /\ [][Scan]_vars
  /\ WF_vars(Scan)

\* Any true majority element must be the final candidate after a full scan.
Correct ==
  \A v \in Values :
    (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq))
      => (seq # <<>> /\ candidate = v)

Inv ==
  /\ pos \in 1..(bound + 1)
  /\ counter \in 0..bound
  /\ candidate \in Values

TypeOKInv == TypeOK /\ Inv
====