---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Value == {A, B, C}
Seqs == UNION { [1 .. n -> Value] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

Init ==
  /\ seq \in Seqs
  /\ pos \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt = 0

Next ==
  \/ pos <= Len(seq)
       /\ LET x == seq[pos] IN
            IF cnt = 0 THEN cand' = x /\ cnt' = 1
            ELSE IF x = cand THEN cnt' = cnt + 1
            ELSE cnt' = cnt - 1
       /\ pos' = pos + 1
       \/ seq' = seq
  \/ pos = Len(seq) + 1
       /\ UNCHANGED <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ seq \in Seqsof(Value)
  /\ pos \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

Correct ==
  \A x \in Value : (2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = x }) > Len(seq))
                     => (cand = x)

\* The inductive pair: candidate and counter stabilize at completion.
Inv ==
  /\ (pos = Len(seq) + 1) => (cnt = 0 \/ cnt = 1)
  /\ (pos = Len(seq) + 1 /\ cnt = 1) => (cand = seq[Len(seq)])

NextStep == pos <= Len(seq)

\* Always reachable: a short walk backs up the scanning position.
SpecStep == Spec /\ WF_vars(NextStep)

====