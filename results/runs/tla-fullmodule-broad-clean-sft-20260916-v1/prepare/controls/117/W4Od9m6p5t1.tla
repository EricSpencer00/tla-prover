---------------------------- MODULE W4Od9m6p5t1 ----------------------------
EXTENDS Naturals

CONSTANTS Ctrl, Breaker, none, MaxClock, TERM

ASSUME MaxClock \in Nat /\ TERM \in Nat /\ TERM > 0

VARIABLES clock, leaseHolder, leaseExp, tripMsgs, tripped
vars == <<clock, leaseHolder, leaseExp, tripMsgs, tripped>>

TypeOK ==
    /\ clock \in 0..MaxClock
    /\ leaseHolder \in Ctrl \cup {none}
    /\ leaseExp \in 0..(MaxClock + TERM)
    /\ tripMsgs \subseteq Breaker
    /\ tripped \subseteq Breaker

Init ==
    /\ clock = 0
    /\ leaseHolder = none
    /\ leaseExp = 0
    /\ tripMsgs = {}
    /\ tripped = {}

AcquireLease(c) ==
    /\ leaseHolder = none \/ clock >= leaseExp
    /\ leaseHolder' = c
    /\ leaseExp' = clock + TERM
    /\ UNCHANGED <<clock, tripMsgs, tripped>>

Renew(c) ==
    /\ leaseHolder = c
    /\ clock < leaseExp
    /\ leaseExp' = clock + TERM
    /\ UNCHANGED <<clock, leaseHolder, tripMsgs, tripped>>

Issue(b) ==
    /\ leaseHolder # none
    /\ clock < leaseExp
    /\ b \notin tripped
    /\ b \notin tripMsgs
    /\ tripMsgs' = tripMsgs \cup {b}
    /\ UNCHANGED <<clock, leaseHolder, leaseExp, tripped>>

Apply(b) ==
    /\ b \in tripMsgs
    /\ tripped' = tripped \cup {b}
    /\ tripMsgs' = tripMsgs \ {b}
    /\ UNCHANGED <<clock, leaseHolder, leaseExp>>

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED <<leaseHolder, leaseExp, tripMsgs, tripped>>

ReleaseLease(c) ==
    /\ leaseHolder = c
    /\ leaseHolder' = none
    /\ UNCHANGED <<clock, leaseExp, tripMsgs, tripped>>

Next ==
    \/ \E c \in Ctrl : AcquireLease(c)
    \/ \E c \in Ctrl : Renew(c)
    \/ \E b \in Breaker : Issue(b)
    \/ \E b \in Breaker : Apply(b)
    \/ Tick
    \/ \E c \in Ctrl : ReleaseLease(c)

Spec == Init /\ [][Next]_vars

AtMostOnceTrip == tripMsgs \cap tripped = {}
=============================================================================