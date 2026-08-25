---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT A, B, C, bound

ValueSet == { A, B, C }

(* BoundedSeq replaces Seq from Sequences *)
BoundedSeq == UNION { [1..n -> ValueSet] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in ValueSet

Count(s, e) == Cardinality({ i \in DOMAIN s : s[i] = e })

Next ==
    IF pos <= Len(seq) THEN
        LET x == seq[pos] IN
        \/ /\ cnt = 0
           /\ cand' = x
           /\ cnt' = 1
           /\ pos' = pos + 1
        \/ /\ cnt > 0 /\ cand = x
           /\ cand' = cand
           /\ cnt' = cnt + 1
           /\ pos' = pos + 1
        \/ /\ cnt > 0 /\ cand # x
           /\ cand' = cand
           /\ cnt' = cnt - 1
           /\ pos' = pos + 1
    ELSE
        UNCHANGED <<seq, pos, cand, cnt>>

vars == <<seq, pos, cand, cnt>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

Inv ==
    /\ cnt \in Nat
    /\ cand \in ValueSet

Correct ==
    (pos > Len(seq)) =>
        ( (∃ e \in ValueSet : Count(seq, e) > Len(seq) / 2)
          => ∃ e \in ValueSet :
                 /\ Count(seq, e) > Len(seq) / 2
                 /\ cand = e )

====