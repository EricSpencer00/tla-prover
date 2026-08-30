---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES cs, want, ticket, nextTicket
vars == <<cs, want, ticket, nextTicket>>

Processes == 1..N

TypeInv ==
    /\ cs \in [Processes -> BOOLEAN]
    /\ want \in [Processes -> BOOLEAN]
    /\ ticket \in [Processes -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ cs = [p \in Processes |-> FALSE]
    /\ want = [p \in Processes |-> FALSE]
    /\ ticket = [p \in Processes |-> 0]
    /\ nextTicket = 0

Request(p) ==
    /\ ~want[p]
    /\ want' = [want EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<cs, ticket, nextTicket>>

Acquire(p) ==
    /\ want[p]
    /\ ~cs[p]
    /\ \A q \in Processes : ~cs[q]
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ want' = [want EXCEPT ![p] = FALSE]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket

Release(p) ==
    /\ cs[p]
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<want, ticket, nextTicket>>

ReleaseAny == \E p \in Processes: Release(p)

Next ==
    \/ \E p \in Processes : Request(p)
    \/ \E p \in Processes : Acquire(p)
    \/ ReleaseAny

MutualExclusion ==
    \A p, q \in Processes : (cs[p] /\ cs[q]) => p = q

Inv == TypeInv /\ MutualExclusion

ISpec == Init /\ [][Next]_vars /\ WF_vars(ReleaseAny)

====