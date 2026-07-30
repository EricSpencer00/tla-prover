---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

ASSUME MaxNat \in Nat /\ N \in Nat /\ N >= 1

VARIABLES ticket, nextTicket, cs

vars == <<ticket, nextTicket, cs>>

TypeOK ==
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ cs \in [1..N -> BOOLEAN]

Init ==
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0
    /\ cs = [p \in 1..N |-> FALSE]

Request(p) ==
    /\ ticket[p] = 0
    /\ nextTicket < MaxNat
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket + 1]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED cs

Enter(p) ==
    /\ ticket[p] # 0
    /\ \A q \in 1..N : cs[q] => ticket[q] <= ticket[p]
    /\ cs[p] = FALSE
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
    /\ cs[p] = TRUE
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED nextTicket

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

ISpec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p, q \in 1..N : (cs[p] /\ cs[q]) => p = q

Inv == TypeOK

====