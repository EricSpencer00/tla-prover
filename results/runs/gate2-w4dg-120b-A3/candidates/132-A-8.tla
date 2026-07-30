---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound
Values == {A, B, C}

\* BoundedSeq is a finite version of the standard Seq constructor; it builds
\* only sequences of length at most "bound" so the state space stays finite.
BoundedSeq == {f \in [1..n -> Values] : n \in 0..bound}

VARIABLES seq, i, cand, cnt
vars == <<seq, i, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ i \in 0..bound
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ cand \in Values
  /\ cnt = 0

Next ==
  \/ \E x \in Values :
       /\ i <= Len(seq)
       /\ IF cnt = 0 THEN /\ cand' = x
                        /\ cnt' = 1
          ELSE IF x = cand THEN cnt' = cnt + 1
          ELSE cnt' = cnt - 1
       /\ seq' = [seq EXCEPT ![i] = x]
       /\ i' = i + 1
  \/ \E s \in BoundedSeq :
       /\ i = Len(seq) + 1
       /\ Len(s) < bound
       /\ i' = i + 1
       /\ seq' = s
       /\ UNCHANGED <<cand, cnt>>

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

Correct ==
  (cnt > 0 /\ i > Len(seq)) => (2 * Cardinality({k \in 1..Len(seq) : seq[k] = cand}) > Len(seq))

\* A naive majority claim is also an invariant here; it is not sufficient on
\* its own but the model checker will catch the counterexample.
Inv ==
  (cnt > 0 /\ i > Len(seq)) => \E x \in Values :
    (\A k \in 1..Len(seq) : seq[k] = x)

Complete == (cnt > 0 /\ i > Len(seq))
====