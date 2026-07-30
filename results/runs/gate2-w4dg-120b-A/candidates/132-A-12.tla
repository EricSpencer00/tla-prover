---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound, Seq

Values == {A, B, C}
Seqs == {s \in [1 .. n -> Values] : n \in 0 .. bound}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ cand \in Values
  /\ count = 0

Next ==
  \/ \E v \in Values :
       /\ pos <= Len(seq)
       /\ IF count = 0
          THEN /\ cand' = v
               /\ count' = 1
          ELSE IF cand = v
               THEN /\ count' = count + 1
               /\ UNCHANGED cand
               /\ UNCHANGED seq
               /\ UNCHANGED pos
          ELSE /\ count' = count - 1
               /\ UNCHANGED cand
               /\ UNCHANGED seq
               /\ UNCHANGED pos
       /\ pos' = IF pos <= Len(seq) THEN pos + 1 ELSE pos
  \/ \E w \in Values :
       /\ pos > Len(seq)
       /\ (seq \in Seqs /\ Len(seq) < bound)
       /\ seq' = [1 .. Len(seq) + 1 |-> [i \in 1 .. (Len(seq) + 1) |-> IF i = Len(seq) + 1 THEN w ELSE seq[i]]]
       /\ pos' = 1
       /\ cand' = w
       /\ count' = 0

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Next)

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 0 .. bound
  /\ cand \in Values
  /\ count \in 0 .. bound

Correct ==
  /\ pos > Len(seq)
  => (\A c \in Values : Cardinality({i \in 1 .. Len(seq) : seq[i] = c}) * 2 > Len(seq) => c = cand)

Inv ==
  /\ cand \in Values
  /\ count \in 0 .. Len(seq)

Properties == Correct /\ Inv

====