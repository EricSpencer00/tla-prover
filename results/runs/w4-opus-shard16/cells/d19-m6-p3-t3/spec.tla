-------------------------- MODULE W4Od19m6p3t3 --------------------------
EXTENDS Naturals

CONSTANTS Patrons, Copies, NoCopy, MaxClock, LeaseDur

VARIABLES
    clock,      \* shared clock
    held,       \* held[p] : copy patron p is holding, or NoCopy
    expiry      \* expiry[p] : clock time at which p's lease lapses

vars == << clock, held, expiry >>

TypeOK ==
    /\ clock \in 0..MaxClock
    /\ held \in [Patrons -> (Copies \cup {NoCopy})]
    /\ expiry \in [Patrons -> 0..(MaxClock + LeaseDur)]

Init ==
    /\ clock = 0
    /\ held = [p \in Patrons |-> NoCopy]
    /\ expiry = [p \in Patrons |-> 0]

ValidHold(p) == (held[p] # NoCopy) /\ (expiry[p] > clock)

\* Reserve a copy only if no other patron validly holds it.
Reserve(p, c) ==
    /\ held[p] = NoCopy
    /\ \A q \in Patrons : (q # p) => ~(held[q] = c /\ expiry[q] > clock)
    /\ held' = [held EXCEPT ![p] = c]
    /\ expiry' = [expiry EXCEPT ![p] = clock + LeaseDur]
    /\ UNCHANGED clock

\* A patron releases its copy explicitly.
Release(p) ==
    /\ held[p] # NoCopy
    /\ held' = [held EXCEPT ![p] = NoCopy]
    /\ UNCHANGED << clock, expiry >>

\* A holder whose lease has lapsed drops the copy.
DropExpired(p) ==
    /\ held[p] # NoCopy
    /\ expiry[p] <= clock
    /\ held' = [held EXCEPT ![p] = NoCopy]
    /\ UNCHANGED << clock, expiry >>

\* Time advances, which lets leases expire.
Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED << held, expiry >>

Next ==
    \/ \E p \in Patrons, c \in Copies : Reserve(p, c)
    \/ \E p \in Patrons : Release(p)
    \/ \E p \in Patrons : DropExpired(p)
    \/ Tick

Spec == Init /\ [][Next]_vars

\* No double allocation: a copy is never validly held by two patrons at once.
NoDoubleAllocation ==
    \A p, q \in Patrons :
        (p # q /\ ValidHold(p) /\ ValidHold(q)) => (held[p] # held[q])

=============================================================================
