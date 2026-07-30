---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}

ELEMENTS(S) == UNION { {Seq[i]} : i \in DOMAIN Seq }
UPPER == CHOOSE n \in Nat : \A m \in Nat : (m <= n) => (m \in DOMAIN Seq)

VARIABLES seq, pos, cand, counter

TypeOK ==
  /\ seq \in Seq
  /\ pos \in 1..(UPPER + 1)
  /\ cand \in Values
  /\ counter \in 0..UPPER

Init ==
  /\ seq \in Seq
  /\ pos = 1
  /\ cand \in Values
  /\ counter = 0

Next ==
  /\ pos <= UPPER
  /\ LET x == seq[pos] IN
       \/ /\ cand = x
          /\ counter' = counter + 1
       \/ \/ /\ counter = 0
            /\ cand' = x
            /\ counter' = 1
          \/ /\ cand # x
            /\ counter' = counter - 1
       \/ UNCHANGED cand
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_<<seq, pos, cand, counter>>

Inv ==
  /\ pos <= UPPER + 1
  /\ (pos = UPPER + 1 => (counter >= 1 => cand \in ELEMENTS(seq)))
  /\ (pos >= 2 => (cand \in {seq[1], seq[pos - 1]}))

Correct ==
  /\ \A a \in Values : (2 * Cardinality({i \in DOMAIN seq : seq[i] = a}) > Cardinality(Seq))
       => (a = cand)

====