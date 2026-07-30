---- MODULE MCMajority ----
EXTENDS Integers, FiniteSets

CONSTANTS A, B, C, bound

ValueSet == {A, B, C}

Seq == UNION { [1 .. n -> ValueSet] : n \in 0 .. bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

Init ==
    /\ seq \in Seq
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

Next ==
    \/ \E x \in ValueSet :
         /\ pos <= Len(seq)
         /\ IF cnt = 0
              THEN /\ cand' = x
                   /\ cnt' = 1
                   /\ pos' = pos + 1
                   /\ UNCHANGED seq
              ELSE IF cand = x
                   THEN /\ cnt' = cnt + 1
                        /\ pos' = pos + 1
                        /\ UNCHANGED <<seq, cand>>
                   ELSE /\ cnt' = cnt - 1
                        /\ pos' = pos + 1
                        /\ UNCHANGED <<seq, cand>>
    \/ \E s \in Seq :
         /\ s # seq
         /\ seq' = s
         /\ UNCHANGED <<pos, cand, cnt>>

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ seq \in Seq
    /\ pos \in 0 .. bound + 1
    /\ cand \in ValueSet
    /\ cnt \in 0 .. bound

Correct ==
    /\ pos > Len(seq)
    /\ \A v \in ValueSet : (2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = v }) > Len(seq)) => v = cand

Inv ==
    /\ pos \in 1 .. Len(seq) + 1
    /\ cand \in ValueSet
    /\ cnt \in 0 .. bound

Spec == Init /\ [][Next]_vars

SpecF == Spec /\ WF_vars(Next)

====