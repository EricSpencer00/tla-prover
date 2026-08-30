---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

SeqSpace == UNION { [1 .. n -> Values] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in SeqSpace
  /\ pos \in 1 .. (bound + 1)
  /\ cand \in Values
  /\ cnt \in 0 .. 2

Init ==
  /\ seq \in SeqSpace
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

Next ==
  \/ \E x \in Values :
       /\ pos <= Len(seq)
       /\ LET y == seq[pos] IN
            /\ IF cnt = 0 THEN cand' = x ELSE cand' = cand
            /\ cnt' = IF cnt = 0 THEN 1
                     ELSE IF y = cand THEN cnt + 1
                     ELSE cnt - 1
       /\ pos' = pos + 1
       /\ seq' = seq
  \/ (pos <= Len(seq) /\ pos' = pos + 1 /\ UNCHANGED <<seq, cand, cnt>>)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Correct ==
  \A e \in Values :
    (Cardinality({ i \in 1 .. Len(seq) : seq[i] = e }) * 2 > Len(seq))
      => (pos > Len(seq) => e = cand)

Inv ==
  (pos > Len(seq) => cnt = 0)

Spec == Spec /\ (\A e \in Values :
  (Cardinality({ i \in 1 .. Len(seq) : seq[i] = e }) * 2 > Len(seq))
    => (pos > Len(seq) => e = cand))

====