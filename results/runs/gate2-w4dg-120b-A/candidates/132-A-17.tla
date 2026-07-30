---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

\* A bounded sequence is a function from a prefix of Nat to Values, together
\* with its length; this keeps the state space finite.
Sequences == {s \in [1..n -> Values] : n \in 0..bound}

VARIABLES seq, pos, cand, cnt

vars == << seq, pos, cand, cnt >>

Init ==
  /\ seq \in Sequences
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* The three-case scan from Boyer-Moore: adopt, increment, decrement.
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       \/ /\ cnt = 0
          /\ cand' = x
          /\ cnt' = 1
       \/ /\ x = cand
          /\ cnt' = cnt + 1
       \/ /\ x # cand
          /\ cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* Invariant: a completed scan with a true majority must have that majority as
\* its candidate.
Correct ==
  (pos > Len(seq) /\ cnt > 0 /\ \A x \in Values : Cardinality({i \in 1..Len(seq) : seq[i] = x}) * 2 > Len(seq))
    => cand \in {x \in Values : Cardinality({i \in 1..Len(seq) : seq[i] = x}) * 2 > Len(seq)}

TypeOK ==
  /\ seq \in Sequences
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

Inv == TypeOK /\ Correct

====