---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

Seqs == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

Init ==
  /\ seq \in Seqs
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ cand \in Values
  /\ count = 0

Scan ==
  /\ pos <= Len(seq)
  /\ IF seq[pos] = cand
       THEN /\ count' = count + 1
            /\ cand' = cand
       ELSE IF count = 0
            THEN /\ cand' = seq[pos]
                 /\ count' = 1
            ELSE /\ cand' = cand
                 /\ count' = count - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Scan]_vars

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ count \in 0 .. bound

Majority(x) == 2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = x }) > Len(seq)

Correct ==
  \A x \in Values : Majority(x) => (pos = Len(seq) + 1 => cand = x)

Inv == \A x \in Values : Majority(x) => cand = x

NextPos == \E p \in Seqs : Init /\ [][Scan]_vars

FutureComplete == TRUE [][NextPos]_vars

====