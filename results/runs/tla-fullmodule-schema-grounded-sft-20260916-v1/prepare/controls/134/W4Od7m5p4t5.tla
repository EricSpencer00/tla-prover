------------------------------ MODULE W4Od7m5p4t5 ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Bays, Slots, Voters

VARIABLES occupied, freeSl, pend, votes

vars == <<occupied, freeSl, pend, votes>>

Quorum == (Cardinality(Voters) \div 2) + 1

TypeOK ==
    /\ occupied \in [Bays -> SUBSET Slots]
    /\ freeSl \in [Bays -> SUBSET Slots]
    /\ pend \in [active: BOOLEAN, bay: Bays, slot: Slots]
    /\ votes \in SUBSET Voters

Init ==
    /\ occupied = [y \in Bays |-> {}]
    /\ freeSl = [y \in Bays |-> Slots]
    /\ pend = [active |-> FALSE,
               bay |-> CHOOSE y \in Bays : TRUE,
               slot |-> CHOOSE s \in Slots : TRUE]
    /\ votes = {}

Propose(y, s) ==
    /\ ~pend.active
    /\ s \in freeSl[y]
    /\ pend' = [active |-> TRUE, bay |-> y, slot |-> s]
    /\ votes' = {}
    /\ UNCHANGED <<occupied, freeSl>>

Vote(v) ==
    /\ pend.active
    /\ v \notin votes
    /\ votes' = votes \cup {v}
    /\ UNCHANGED <<occupied, freeSl, pend>>

Place ==
    /\ pend.active
    /\ Cardinality(votes) >= Quorum
    /\ pend.slot \in freeSl[pend.bay]
    /\ occupied' = [occupied EXCEPT ![pend.bay] = @ \cup {pend.slot}]
    /\ freeSl' = [freeSl EXCEPT ![pend.bay] = @ \ {pend.slot}]
    /\ pend' = [pend EXCEPT !.active = FALSE]
    /\ votes' = {}

Withdraw ==
    /\ pend.active
    /\ pend' = [pend EXCEPT !.active = FALSE]
    /\ votes' = {}
    /\ UNCHANGED <<occupied, freeSl>>

AdminPlace(y, s) ==
    /\ s \in freeSl[y]
    /\ occupied' = [occupied EXCEPT ![y] = @ \cup {s}]
    /\ freeSl' = [freeSl EXCEPT ![y] = @ \ {s}]
    /\ UNCHANGED <<pend, votes>>

Remove(y, s) ==
    /\ s \in occupied[y]
    /\ occupied' = [occupied EXCEPT ![y] = @ \ {s}]
    /\ freeSl' = [freeSl EXCEPT ![y] = @ \cup {s}]
    /\ UNCHANGED <<pend, votes>>

Next ==
    \/ \E y \in Bays, s \in Slots : Propose(y, s)
    \/ \E v \in Voters : Vote(v)
    \/ Place
    \/ Withdraw
    \/ \E y \in Bays, s \in Slots : AdminPlace(y, s)
    \/ \E y \in Bays, s \in Slots : Remove(y, s)

Spec == Init /\ [][Next]_vars

BayPartition ==
    \A y \in Bays :
        /\ occupied[y] \cup freeSl[y] = Slots
        /\ occupied[y] \cap freeSl[y] = {}

=============================================================================