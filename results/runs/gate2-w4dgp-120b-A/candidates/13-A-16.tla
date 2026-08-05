---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES using, ticket, nextTicket, cs

vars == <<using, ticket, nextTicket, cs>>

TypeOK ==
    /\ using \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ cs \in [1..N -> BOOLEAN]

MutualExclusion ==
    \A i \in 1..N : cs[i] => (using[i] /\ \A j \in 1..N : cs[j] => j=i)

Inv ==
    /\ MutualExclusion
    /\ (using[1] => ticket[1] = 0)

Init == UNCHANGED vars

Request(i) ==
    /\ ~using[i]
    /\ using' = [using EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED cs

Enter(i) ==
    /\ using[i]
    /\ ~cs[i]
    /\ \A j \in 1..N : ~ cs[j] \/ ticket[j] > ticket[i]
    /\ cs' = [cs EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<using, ticket, nextTicket>>

Exit(i) ==
    /\ cs[i]
    /\ cs' = [cs EXCEPT ![i] = FALSE]
    /\ using' = [using EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<ticket, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ TRUE

====