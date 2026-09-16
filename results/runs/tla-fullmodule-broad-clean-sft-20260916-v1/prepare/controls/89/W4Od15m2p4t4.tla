---- MODULE W4Od15m2p4t4 ----
EXTENDS Integers

Parties == {"exchange", "member", "risk"}
MaxLots == 3
Sizes == 1..2

VARIABLES stage, ballot, proposed, booked, bookCap

vars == <<stage, ballot, proposed, booked, bookCap>>

TypeOK ==
    /\ stage \in {"idle", "voting", "committed", "unwinding"}
    /\ ballot \in [Parties -> {"unset", "yes", "no"}]
    /\ proposed \in 0..2
    /\ booked \in 0..MaxLots
    /\ bookCap \in 1..MaxLots

Init ==
    /\ stage = "idle"
    /\ ballot = [p \in Parties |-> "unset"]
    /\ proposed = 0
    /\ booked = 0
    /\ bookCap = MaxLots

ProposeBlock(n) ==
    /\ stage = "idle"
    /\ n \in Sizes
    /\ booked + n <= bookCap
    /\ proposed' = n
    /\ stage' = "voting"
    /\ UNCHANGED <<ballot, booked, bookCap>>

Vote(p, v) ==
    /\ stage = "voting"
    /\ ballot[p] = "unset"
    /\ v \in {"yes", "no"}
    /\ ballot' = [ballot EXCEPT ![p] = v]
    /\ UNCHANGED <<stage, proposed, booked, bookCap>>

Commit ==
    /\ stage = "voting"
    /\ \A p \in Parties : ballot[p] = "yes"
    /\ stage' = "committed"
    /\ UNCHANGED <<ballot, proposed, booked, bookCap>>

Abort ==
    /\ stage = "voting"
    /\ \E p \in Parties : ballot[p] = "no"
    /\ stage' = "unwinding"
    /\ UNCHANGED <<ballot, proposed, booked, bookCap>>

WriteBlock ==
    /\ stage = "committed"
    /\ booked' = booked + proposed
    /\ stage' = "unwinding"
    /\ UNCHANGED <<ballot, proposed, bookCap>>

Unwind ==
    /\ stage = "unwinding"
    /\ stage' = "idle"
    /\ ballot' = [p \in Parties |-> "unset"]
    /\ proposed' = 0
    /\ UNCHANGED <<booked, bookCap>>

Retune(c) ==
    /\ stage = "idle"
    /\ c \in 1..MaxLots
    /\ c # bookCap
    /\ c >= booked
    /\ bookCap' = c
    /\ UNCHANGED <<stage, ballot, proposed, booked>>

CrossAuction ==
    /\ stage = "idle"
    /\ booked > 0
    /\ booked' = 0
    /\ UNCHANGED <<stage, ballot, proposed, bookCap>>

Step ==
    \/ \E n \in Sizes : ProposeBlock(n)
    \/ \E p \in Parties, v \in {"yes", "no"} : Vote(p, v)
    \/ Commit
    \/ Abort
    \/ WriteBlock
    \/ Unwind
    \/ \E c \in 1..MaxLots : Retune(c)
    \/ CrossAuction

Spec == Init /\ [][Step]_vars

BookNeverOverfilled ==
    /\ booked <= bookCap
    /\ stage = "committed" =>
         /\ \A p \in Parties : ballot[p] = "yes"
         /\ proposed \in Sizes
         /\ booked + proposed <= bookCap
    /\ stage = "idle" =>
         /\ proposed = 0
         /\ \A p \in Parties : ballot[p] = "unset"
====