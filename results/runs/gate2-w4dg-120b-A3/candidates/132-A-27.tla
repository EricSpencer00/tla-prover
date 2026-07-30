---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}
BoundedSeq(A) == { s \in [0..bound -> Values] : s[0] < bound }

VARIABLES seq, pos, cand, count
vars == << seq, pos, cand, count >>

TypeOK ==
  /\ seq \in BoundedSeq(A)
  /\ pos \in 0..bound
  /\ cand \in Values
  /\ count \in 0..bound

Init ==
  /\ seq \in BoundedSeq(A)
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

Step ==
  /\ pos < bound
  /\ LET x == seq[pos] IN
       /\ IF count = 0
          THEN /\ cand' = x
               /\ count' = 1
          ELSE IF x = cand
               THEN count' = count + 1
               ELSE count' = count - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Step]_vars

Correct ==
  \A s \in Values : (\A i \in 1..pos : seq[i] = s) => cand = s
  /\ \A i \in 1..pos : seq[i] # cand => count <= 2 * i - 1

Inv ==
  /\ CountCandFor(cand, seq, bound) <= CountCandFor(cand, seq, pos) + (pos - bound)
  /\ count >= 0

Repeats == \E s \in Values : \A i \in 1..pos : seq[i] = s

CountCandFor(c, s, p) ==
  Cardinality({i \in 1..p : s[i] = c})

EventuallyRepeats ==
  \A i \in 1..bound : TRUE \U (pos >= i /\ Repeats)

Properties == EventuallyRepeats

====