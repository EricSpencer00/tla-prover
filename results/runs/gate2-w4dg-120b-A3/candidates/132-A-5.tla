---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq is a finite version of the standard Seq operator from Sequences
\* that keeps the state space finite for model checking; it is defined here
\* while the name Seq from Sequences is left untouched.
BoundedSeq(n) == IF n = 0 THEN << >> ELSE CHOOSE s \in Seq(Vals) : Len(s) = n

VARIABLES seq, pos, cand, ctr

vars == << seq, pos, cand, ctr >>

Init ==
  /\ \E n \in 0..bound, s \in BoundedSeq(n) : seq = s
  /\ pos = 1
  /\ \E c \in Values : cand = c
  /\ ctr = 0

\* The three-case logic of Boyer-Moore: adopt a new candidate, increment,
\* or decrement, driven by the counter reaching zero.
Next ==
  \/ (\E x \in Values :
        /\ pos <= Len(seq)
        /\ (IF ctr = 0 THEN /\ cand' = x /\ ctr' = 1
                        ELSE IF cand = x THEN /\ ctr' = ctr + 1
                                          ELSE /\ ctr' = ctr - 1)
        /\ pos' = pos + 1
        /\ UNCHANGED seq)
  \/ (pos <= Len(seq) /\ "\A x \in Values : TRUE" /\ UNCHANGED << seq, pos, cand, ctr >>)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= bound
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ ctr \in 0..bound

\* The candidate after a complete scan is the only element that can hold a
\* true majority in the sequence; no other value may dominate it.
Correct ==
  \A v \in Values :
    (\E m \in 1..Len(seq) :
       /\ seq[m] = v
       /\ Cardinality({i \in 1..Len(seq) : seq[i] = v}) * 2 > Len(seq))
      => v = cand

Inv ==
  /\ (pos > Len(seq) => ctr = 1)
  /\ (pos > Len(seq) => cand = seq[1])
  /\ (pos > Len(seq) /\ cand \notin {seq[i] : i \in 1..Len(seq)} => ctr = 0)

Complete == pos > Len(seq)

====