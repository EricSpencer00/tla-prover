---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

CONSTANTS Values
Values == {A, B, C}

\* Finite version of the standard Seq operator: only sequences whose
\* length is at most the configured bound are admitted.
BoundedSeq == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, ctr
vars == <<seq, pos, cand, ctr>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1 .. (IF seq = [1 .. 0 -> Values] THEN 1 ELSE Len(seq) + 1)
  /\ cand \in Values
  /\ ctr \in 0 .. bound

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in Values
  /\ ctr = 0

\* Main majority-vote step: three cases depending on the counter.
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF ctr = 0 THEN
         /\ cand' = x
         /\ ctr' = 1
       ELSE IF cand = x THEN
         /\ ctr' = ctr + 1
       ELSE
         /\ ctr' = ctr - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

\* Once the scan has completed, it may stutter.
Done ==
  /\ pos = Len(seq) + 1
  /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ SF_vars(Step) /\ WF_vars(Done)

Correct ==
  /\ (ctr > 0) => (2 * ctr > Len(seq))
  /\ (ctr = 0) => (2 * ctr <= Len(seq))

Inv ==
  /\ ctr >= 0
  /\ ctr <= bound

\* All safety properties from the main spec, collected under the cfg name.
TypeOKInv == TypeOK
CorrectInv == Correct
InvInv == Inv

SpecFormula == Spec
====