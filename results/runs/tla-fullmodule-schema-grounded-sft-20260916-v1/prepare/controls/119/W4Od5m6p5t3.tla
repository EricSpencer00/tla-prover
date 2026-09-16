---- MODULE W4Od5m6p5t3 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Players, LeaseDur, MaxTime, NULL

VARIABLES clock, leaseOwner, leaseExpiry, committed, committedAt, commitDeadline
vars == << clock, leaseOwner, leaseExpiry, committed, committedAt, commitDeadline >>

TypeOK ==
    /\ clock \in 0 .. MaxTime
    /\ leaseOwner \in Players \cup {NULL}
    /\ leaseExpiry \in 0 .. (MaxTime + LeaseDur)
    /\ committed \in BOOLEAN
    /\ committedAt \in 0 .. MaxTime
    /\ commitDeadline \in 0 .. (MaxTime + LeaseDur)

Init ==
    /\ clock = 0
    /\ leaseOwner = NULL
    /\ leaseExpiry = 0
    /\ committed = FALSE
    /\ committedAt = 0
    /\ commitDeadline = 0

Acquire(p) ==
    /\ leaseOwner = NULL
    /\ leaseOwner' = p
    /\ leaseExpiry' = clock + LeaseDur
    /\ UNCHANGED << clock, committed, committedAt, commitDeadline >>

Renew(p) ==
    /\ leaseOwner = p
    /\ clock < leaseExpiry
    /\ leaseExpiry' = clock + LeaseDur
    /\ UNCHANGED << clock, leaseOwner, committed, committedAt, commitDeadline >>

Tick ==
    /\ clock < MaxTime
    /\ clock' = clock + 1
    /\ UNCHANGED << leaseOwner, leaseExpiry, committed, committedAt, commitDeadline >>

Expire ==
    /\ leaseOwner # NULL
    /\ clock >= leaseExpiry
    /\ leaseOwner' = NULL
    /\ UNCHANGED << clock, leaseExpiry, committed, committedAt, commitDeadline >>

Commit(p) ==
    /\ leaseOwner = p
    /\ clock < leaseExpiry
    /\ ~committed
    /\ committed' = TRUE
    /\ committedAt' = clock
    /\ commitDeadline' = leaseExpiry
    /\ UNCHANGED << clock, leaseOwner, leaseExpiry >>

ResetRound ==
    /\ clock = MaxTime
    /\ clock' = 0
    /\ leaseOwner' = NULL
    /\ leaseExpiry' = 0
    /\ committed' = FALSE
    /\ committedAt' = 0
    /\ commitDeadline' = 0

Next ==
    \/ \E p \in Players : Acquire(p)
    \/ \E p \in Players : Renew(p)
    \/ Tick
    \/ Expire
    \/ \E p \in Players : Commit(p)
    \/ ResetRound

Spec == Init /\ [][Next]_vars

CommitWithinLease ==
    committed => committedAt < commitDeadline
====