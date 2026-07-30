---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

Range == 0 .. bound

VARIABLES seq, pos, cand, ct

vars == <<seq, pos, cand, ct>>

TypeOK ==
  /\ seq \in [1 .. bound -> Values]
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ ct \in 0 .. bound

Init ==
  /\ seq \in [1 .. bound -> Values]
  /\ pos = 1
  /\ cand \in Values
  /\ ct = 0

Next ==
  /\ \/ \E v \in Values :
        /\ pos <= bound
        /\ seq' = [seq EXCEPT ![pos] = v]
        /\ pos' = pos + 1
        /\ IF ct = 0 THEN cand' = v /\ ct' = 1
           ELSE IF cand = v THEN ct' = ct + 1 /\ cand' = cand
           ELSE ct' = ct - 1 /\ cand' = cand
  /\ UNCHANGED <<seq, pos, cand, ct>>

Spec == Init /\ [][Next]_vars

\* The main correctness property: any true majority element must equal the
\* candidate after a complete scan.
Correct ==
  \A v \in Values :
    /\ 2 * Cardinality({i \in 1 .. bound : seq[i] = v}) > bound
    /\ (pos > bound) => (cand = v)

\* The inductive invariant carried over from the main spec.
Inv ==
  /\ Cardinality({i \in 1 .. bound : seq[i] = cand}) >= ct
  /\ (ct = 0 => (\E c \in Values : cand = c))

\* The bounded sequence construction: all sequences up to the bound length.
BoundedSeq == [1 .. bound -> Values]

====