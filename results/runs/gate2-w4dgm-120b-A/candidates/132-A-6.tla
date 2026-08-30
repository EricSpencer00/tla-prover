---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The three distinct values that can appear in sequences; bound is the
\* maximum length of any sequence considered in this model.

Values == {A, B, C}

\* BoundedSeq is the finite version of Seq used here to keep the model
\* checkable; it yields exactly the sequences of length up to bound.
BoundedSeq(set) == UNION { Seq(V) : V \in [1..n -> set] : n \in 0..bound }

VARIABLES seq, pos, candidate, counter

vars == <<seq, pos, candidate, counter>>

TypeOK ==
  /\ seq \in BoundedSeq(Values)
  /\ pos \in 1..(Len(seq) + 1)
  /\ candidate \in Values
  /\ counter \in 0..Max(counter, 1)

Init ==
  /\ seq \in BoundedSeq(Values)
  /\ pos = 1
  /\ candidate \in Values
  /\ counter = 0

\* The three-case logic: first element of a fresh candidate, matching
\* continuation, or conflict that forces a step back.
Step ==
  /\ pos <= Len(seq)
  /\ LET elem == seq[pos] IN
       candidate' = IF counter = 0 \/ elem # candidate THEN elem ELSE candidate
       counter' = IF counter = 0 \/ elem # candidate THEN 1 ELSE counter + 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

\* A mismatch at a non-empty counter decrements the counter; the candidate
\* stays put and the scan moves on.
StepDown ==
  /\ pos <= Len(seq)
  /\ seq[pos] # candidate
  /\ counter > 0
  /\ counter' = counter - 1
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq, candidate>>

\* An element equal to the current candidate increments the counter.
StepUp ==
  /\ pos <= Len(seq)
  /\ seq[pos] = candidate
  /\ counter' = counter + 1
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq, candidate>>

\* A mismatch with an empty counter adopts the element as the new
\* candidate and starts a fresh run of it.
Restart ==
  /\ pos <= Len(seq)
  /\ counter = 0
  /\ seq[pos] # candidate
  /\ candidate' = seq[pos]
  /\ counter' = 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step \/ StepDown \/ StepUp \/ Restart

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Step) /\ WF_vars(StepDown) /\ WF_vars(StepUp) /\ WF_vars(Restart)

\* SAFETY: a true majority must equal the candidate after a complete scan.
Correct ==
  \A a \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = a }) > Len(seq))
                      => a = candidate

\* INVARIANT: the counter never exceeds the length of the scan prefix.
Inv == counter <= pos - 1

\* LIVENESS: the scan always eventually completes (weak fairness).
Complete == <>(pos > Len(seq))
====