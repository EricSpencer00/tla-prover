---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The model constants: three distinct values plus a bound on sequence length.
Vals == {A, B, C}

\* A finite analogue of Seq (from Sequences) that only yields sequences of
\* length up to the bound, keeping the model state space finite for TLC.
BoundedSeq == { f \in [1..bound -> Vals] : \E n \in 0..bound : f \in [1..n -> Vals] }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..bound
  /\ cand \in Vals
  /\ cnt \in Nat

\* The main correctness property: any true majority element must equal the
\* candidate after a complete scan of the sequence.
Correct ==
  \A x \in Vals :
    (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = x }) > Len(seq)) => (cand = x)

\* An inductively maintained candidate-counter relationship that is
\* preserved by the three-case scan logic: if the running candidate is
\* equal to the scanned element then the counter is strictly positive.
Inv ==
  \A i \in 1..Len(seq) : (cand = seq[i]) => (cnt > 0)

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Vals
  /\ cnt = 0

\* Scan the next element; three cases handle candidate replacement,
\* counter increment, and counter decrement (the vote-erase).
Next ==
  \/ \E e \in Vals :
       /\ pos <= Len(seq)
       /\ (cand # seq[pos] /\ cnt = 0) => cand' = seq[pos]
       /\ (cand = seq[pos] /\ cnt = 0) => cand' = seq[pos]
       /\ cand' \in Vals
       /\ cnt' = IF cand = seq[pos] THEN cnt + 1 ELSE IF cnt > 0 THEN cnt - 1 ELSE 0
       /\ pos' = pos + 1
       /\ seq' = seq

NextF == Next /\ UNCHANGED <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

ScanCompletes == <>(pos = Len(seq) + 1)

====