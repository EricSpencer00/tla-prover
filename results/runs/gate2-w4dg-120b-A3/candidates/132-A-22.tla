---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound

\* The value set is a fixed set of three distinct model values.
Values == {A, B, C}

\* Sequences are modelled as finite functions from a prefix of the
\* natural numbers to Values, rather than using the standard Seq
\* operator, which would be infinite.  This keeps the model finite.
BoundedSeq == { f \in [1..bound -> Values] : TRUE }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

\* No majority element is ever lost: when the scan has completed, any
\* true majority element must be the surviving candidate.
Correct ==
  (pos = bound + 1 /\ 2 * Cardinality({ i \in 1..bound : seq[i] = cand }) > bound)
    => \A e \in Values : (2 * Cardinality({ i \in 1..bound : seq[i] = e }) > bound) => (e = cand)

Inv ==
  /\ cnt >= 0
  /\ (pos = 1) => (cnt = 0)
  /\ (cnt = 0) => (\A e \in Values : e # cand)

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ \E c \in Values : cand = c
  /\ cnt = 0

\* Scan the next element with the Boyer-Moore three-case logic.
Step ==
  /\ pos <= bound
  /\ LET x == seq[pos] IN
       IF cnt = 0 THEN /\ cand' = x
                     /\ cnt' = 1
       ELSE IF x = cand THEN /\ cnt' = cnt + 1
       ELSE /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars

FiniteFairness == WF_vars(Step)

Props == FiniteFairness

\* Deadlock checking is disabled in the configuration.
SpecWithNoDC == Spec
====