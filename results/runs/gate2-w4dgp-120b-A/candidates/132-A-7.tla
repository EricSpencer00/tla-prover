---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* The model values for the Boyer-Moore majority vote are three distinct
\* elements. The bound limits the longest input sequence so the state space
\* stays finite for model checking. Sequences are taken from the bounded
\* construction below instead of the standard Seq operator.
Values == {A, B, C}

RECURSIVE BoundedSeq(_)
BoundedSeq(n) == IF n = 0 THEN {<<>>} ELSE
  UNION {SeqOf(m) : m \in 0..n}

VARIABLES seq, pos, cand, cnt

TypeOK ==
  /\ seq \in BoundedSeq(bound)
  /\ pos \in Nat
  /\ cand \in Values
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq(bound)
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* Scan the next element with the Boyer-Moore three-case logic.
Scan ==
  /\ pos <= Len(seq)
  /\ LET v == seq[pos] IN
       IF cnt = 0
       THEN /\ cand' = v
            /\ cnt' = 1
       ELSE IF cand = v
            THEN cnt' = 1 + cnt
            ELSE cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Scan

\* Any element that is truly a majority of the scanned sequence must equal
\* the candidate at the end of the scan -- the Boyer-Moore guarantee.
Correct ==
  \A v \in Values :
    (Card({i \in 1..Len(seq) : seq[i] = v}) * 2 > Len(seq)) =>
      (pos = Len(seq) + 1 => cand = v)

\* The usual type-correctness plus the same majority implication as a
\* semantic safety property (not derived from the type-correctness check).
Inv ==
  /\ TypeOK
  /\ \A v \in Values :
       (Card({i \in 1..Len(seq) : seq[i] = v}) * 2 > Len(seq)) =>
         (pos = Len(seq) + 1 => cand = v)

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>
            /\ SF_vars(Scan)

\* The scan always eventually reaches the end of the sequence.
Eventual ==
  WF_vars(Scan)

ASSUME bound \in Nat

====