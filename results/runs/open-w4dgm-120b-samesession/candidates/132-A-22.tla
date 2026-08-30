---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

\* A bounded sequence: only functions with a domain of the form 1..n are
\* admitted, and n is capped by the bound, so the state space stays finite.
BoundedSeq == { f \in [1..bound -> Values] : \A i \in 1..bound : i <= Len(f) => f[i] \in Values }

Init ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in Values
  /\ counter = 0


\* The three-case update: adopt a new candidate when the counter is zero,
\* increment when the element matches the candidate, and decrement otherwise.
Next ==
  \/ pos <= Len(seq)
       /\ LET x == seq[pos] IN
            /\ IF counter = 0 THEN cand' = x /\ counter' = 1
               ELSE IF x = cand THEN cand' = cand /\ counter' = counter + 1
               ELSE cand' = cand /\ counter' = counter - 1
            /\ pos' = pos + 1
            /\ UNCHANGED seq
  \/ pos <= Len(seq) /\ seq' = [seq EXCEPT ![pos] = cand] /\ UNCHANGED <<pos, cand, counter>>
  \/ pos > Len(seq) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(NEXT)

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ counter \in 0..bound

\* Main correctness claim: an element that is a true majority of the whole
\* scan must equal the candidate the scan left behind in the end.
Correct ==
  (pos = Len(seq) + 1 /\ \E a \in Values : \A i \in 1..Len(seq) : seq[i] = a) => cand = seq[1]

\* The candidate stays a possible majority: it never trails the scan too far
\* behind the count that the scan has built up so far.
Inv ==
  (pos <= Len(seq) /\ counter > 0) => cand \in { seq[i] : i \in 1..(pos - 1) }

Complete == pos > Len(seq)

ScanEventuallyCompletes == <>Complete

====