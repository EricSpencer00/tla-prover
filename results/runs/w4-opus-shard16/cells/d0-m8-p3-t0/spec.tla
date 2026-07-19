-------------------------- MODULE W4Od0m8p3t0 --------------------------
EXTENDS Naturals

CONSTANTS Surgeons, Slots, NoOne

VARIABLES
    coarse,     \* holder of the coarse day-lock, or NoOne
    claims,     \* claims[sg] : set of slots surgeon sg holds
    crashed     \* set of silently-crashed surgeons

vars == << coarse, claims, crashed >>

TypeOK ==
    /\ coarse \in (Surgeons \cup {NoOne})
    /\ claims \in [Surgeons -> SUBSET Slots]
    /\ crashed \subseteq Surgeons

Init ==
    /\ coarse = NoOne
    /\ claims = [sg \in Surgeons |-> {}]
    /\ crashed = {}

AcquireCoarse(sg) ==
    /\ sg \notin crashed
    /\ coarse = NoOne
    /\ coarse' = sg
    /\ UNCHANGED << claims, crashed >>

ReleaseCoarse(sg) ==
    /\ sg \notin crashed
    /\ coarse = sg
    /\ coarse' = NoOne
    /\ UNCHANGED << claims, crashed >>

\* Under the coarse lock, claim a fine slot only if no one else holds it.
Book(sg, s) ==
    /\ coarse = sg
    /\ sg \notin crashed
    /\ \A q \in Surgeons : (q # sg) => (s \notin claims[q])
    /\ s \notin claims[sg]
    /\ claims' = [claims EXCEPT ![sg] = @ \cup {s}]
    /\ UNCHANGED << coarse, crashed >>

Cancel(sg, s) ==
    /\ coarse = sg
    /\ sg \notin crashed
    /\ s \in claims[sg]
    /\ claims' = [claims EXCEPT ![sg] = @ \ {s}]
    /\ UNCHANGED << coarse, crashed >>

Crash(sg) ==
    /\ sg \notin crashed
    /\ crashed' = crashed \cup {sg}
    /\ UNCHANGED << coarse, claims >>

\* The scheduler reclaims the coarse lock from a crashed holder.
Reclaim ==
    /\ coarse \in crashed
    /\ coarse' = NoOne
    /\ UNCHANGED << claims, crashed >>

Recover(sg) ==
    /\ sg \in crashed
    /\ crashed' = crashed \ {sg}
    /\ UNCHANGED << coarse, claims >>

Next ==
    \/ \E sg \in Surgeons : AcquireCoarse(sg)
    \/ \E sg \in Surgeons : ReleaseCoarse(sg)
    \/ \E sg \in Surgeons, s \in Slots : Book(sg, s)
    \/ \E sg \in Surgeons, s \in Slots : Cancel(sg, s)
    \/ \E sg \in Surgeons : Crash(sg)
    \/ Reclaim
    \/ \E sg \in Surgeons : Recover(sg)

Spec == Init /\ [][Next]_vars

\* No double allocation: distinct surgeons hold disjoint sets of slots.
NoDoubleBooking ==
    \A p, q \in Surgeons : (p # q) => (claims[p] \cap claims[q] = {})

=============================================================================
