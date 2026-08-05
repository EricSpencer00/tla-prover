---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, candidate, counter

vars == <<seq, pos, candidate, counter>>

BoundedSeq(f) ==
  /\ f # [n \in 1..(bound + 1) |-> IF n <= bound THEN A ELSE A]
  /\ \A i \in DOMAIN f : f[i] \in Values

TypeOK ==
  /\ seq \in UNION {BoundedSeq([n \in 1..k |-> Values]) : k \in 0..bound}
  /\ pos \in 1..(IF seq = [] THEN 1 ELSE Len(seq) + 1)
  /\ candidate \in Values
  /\ counter \in 0..bound

Inits ==
  \E s \in UNION {BoundedSeq([n \in 1..k |-> Values]) : k \in 0..bound} :
    /\ seq = s
    /\ pos = 1
    /\ \E c \in Values : candidate = c
    /\ counter = 0

Majority(v) ==
  Cardinality({i \in DOMAIN seq : seq[i] = v}) * 2 > Len(seq)

NextStep ==
  \/ (\E c \in Values :
        /\ pos # Len(seq) + 1
        /\ candidate' = c
        /\ counter' = counter + 1
        /\ pos' = pos + 1
        /\ UNCHANGED seq)
  \/ (\E c \in Values :
        /\ pos # Len(seq) + 1
        /\ seq[pos] = c
        /\ candidate' = candidate
        /\ counter' = IF counter > 0 THEN counter + 1 ELSE counter
        /\ pos' = pos + 1
        /\ UNCHANGED seq)
  \/ (\E c \in Values :
        /\ pos # Len(seq) + 1
        /\ seq[pos] # c
        /\ candidate' = candidate
        /\ counter' = IF counter > 0 THEN counter - 1 ELSE counter
        /\ pos' = pos + 1
        /\ UNCHANGED seq)
  \/ (pos = Len(seq) + 1 /\ UNCHANGED vars)

Spec ==
  /\ Inits
  /\ [][NextStep]_vars
  /\ WF_vars(NextStep)

Correct ==
  \A v \in Values : Majority(v) => (pos = Len(seq) + 1 => candidate = v)

Inv ==
  /\ pos = Len(seq) + 1 => candidate = seq[1]
  /\ (pos <= Len(seq) + 1 => \/ (pos <= Len(seq) /\ candidate = seq[pos])
       \/ (pos = Len(seq) + 1 /\ candidate = seq[1]))

====