---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
NoVal  == "none"

VARIABLES seq, pos, cand, count
vars == <<seq, pos, cand, count>>

\* A bounded version of the standard Seq operator used as an adaptor so the
\* model stays finite for model checking. It is defined here, not declared.
Seq(s) == s

InitStates == {s \in [1..n -> Values] : n \in 0..bound}

TypeOK ==
  /\ seq \in InitStates
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in Values \cup {NoVal}
  /\ count \in Nat

Init ==
  /\ seq \in InitStates
  /\ pos = 1
  /\ cand \in Values \cup {NoVal}
  /\ count = 0

\* The Boyer-Moore scan: three cases in one step, each updating the position
\* together with the candidate/counter as appropriate.
Next ==
  \/ (\E v \in Values :
        /\ pos <= Len(seq)
        /\ cand = NoVal
        /\ cand' = v
        /\ count' = 1
        /\ pos' = pos + 1
        \/ seq' = seq)
  \/ (\E v \in Values :
        /\ pos <= Len(seq)
        /\ cand # NoVal
        /\ v = cand
        /\ count' = count + 1
        /\ pos' = pos + 1
        /\ seq' = seq
        /\ cand' = cand)
  \/ (\E v \in Values :
        /\ pos <= Len(seq)
        /\ cand # NoVal
        /\ v # cand
        /\ count > 0
        /\ count' = count - 1
        /\ pos' = pos + 1
        /\ seq' = seq
        /\ cand' = cand
       )
  \/ (pos > Len(seq) /\ seq' = seq /\ pos' = pos /\ cand' = cand /\ count' = count)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next) /\ WF_vars(Next) /\ WF_vars(Next) /\ WF_vars(Next)

\* Any true majority element must equal the candidate the scan would name on
\* completing the whole sequence.
Correct ==
  \A v \in Values :
    (Cardinality({i \in 1..Len(seq) : seq[i] = v}) * 2 > Len(seq))
      => (cand = v \/ pos <= Len(seq)

Inv == \A v \in Values : (2 * count > (Len(seq) - pos + 1)) => cand = v

\* A true majority, if any, must survive whatever the Boyer-Moore scan does.
MajoritySurvives == Correct

\* A strict majority is eventually identified: the scan always completes, and
\* the invariant is what makes completion meaningful with respect to the data.
Progress == pos > Len(seq)

====