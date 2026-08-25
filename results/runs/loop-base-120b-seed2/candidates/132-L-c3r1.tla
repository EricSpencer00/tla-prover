---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

Values == { A, B, C }

(* BoundedSeq replaces the usual Seq, restricting length to at most bound *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

Init ==
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt'  = 1
          ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
       /\ i' = i + 1
    \/ /\ i > Len(seq)
       /\ UNCHANGED << seq, i, cand, cnt >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat
    /\ i <= Len(seq) + 1

Count(s, v) ==
    Cardinality({ j \in DOMAIN s : s[j] = v })

Correct ==
    (i = Len(seq) + 1) =>
        ( (\E m \in Values : Count(seq, m) > Len(seq) / 2) => cand = m)

Inv == TypeOK

====