---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES stage, want, ticket, nextTicket

vars == <<stage, want, ticket, nextTicket>>

Stages == {"idle", "waiting", "critical"}

TypeOK ==
    /\ stage \in [1..N -> Stages]
    /\ want \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

Init ==
    /\ stage = [p \in 1..N |-> "idle"]
    /\ want = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0

Request(p) ==
    /\ ~want[p]
    /\ want' = [want EXCEPT ![p] = TRUE]
    /\ stage' = [stage EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<ticket, nextTicket>>

Grant(p) ==
    /\ stage[p] = "waiting"
    /\ want[p]
    /\ nextTicket > 0
    /\ \A q \in 1..N : stage[q] # "critical"
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ stage' = [stage EXCEPT ![p] = "critical"]
    /\ nextTicket' = IF nextTicket = MaxNat THEN 1 ELSE nextTicket + 1
    /\ UNCHANGED want

Release(p) ==
    /\ stage[p] = "critical"
    /\ stage' = [stage EXCEPT ![p] = "idle"]
    /\ want' = [want EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, nextTicket>>

Next ==
    \/ \E p \in 1..N : Request(p) \/ Grant(p) \/ Release(p)

MutualExclusion ==
    \A p, q \in 1..N : (stage[p] = "critical" /\ stage[q] = "critical") => p = q

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][Next]_vars
====