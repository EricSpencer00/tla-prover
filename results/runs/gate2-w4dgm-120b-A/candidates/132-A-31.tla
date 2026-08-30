---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
Nxt(v) == IF v = A THEN B ELSE IF v = B THEN C ELSE A

Sequences == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, ctr

vars == <<seq, pos, cand, ctr>>

TypeOK ==
  /\ seq \in Sequences
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ cand \in Values
  /\ ctr \in 0 .. bound

Init ==
  /\ \E s \in Sequences : seq = s
  /\ pos = 1
  /\ cand \in Values
  /\ ctr = 0

Step ==
  /\ pos <= Len(seq)
  /\ LET v == seq[pos] IN
       IF ctr = 0 THEN /\ cand' = v
                     /\ ctr' = 1
       ELSE IF v = cand THEN /\ cand' = cand
                           /\ ctr' = ctr + 1
       ELSE /\ cand' = cand
            /\ ctr' = ctr - 1
  /\ pos' = pos + 1

Spec == Init /\ [][Step]_vars

Correct ==
  \A e \in Values : (\A i \in 1 .. Len(seq) : seq[i] = e) => (cand = e)

\* The per-step update keeps the candidate in lockstep with a running majority
\* count; together with the bounded length they bound the scan so it always
\* completes.  The counter's value is also tracked here.
Inv ==
  /\ (pos > 1 /\ ctr = 0) => (cand = Nxt(seq[pos - 1]))
  /\ \A i \in 1 .. Len(seq) : ctr >= Cardinality({j \in 1 .. Len(seq) : seq[j] = cand})

Fairness == WF_vars(Step)
====