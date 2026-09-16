---------------------------- MODULE W4Od14m6p5t5 ----------------------------
EXTENDS Naturals

VARIABLES
    phase,         \* "armed" or "released" : state of the one-time drop
    releaseCount,  \* how many times the irreversible retardant drop happened
    leased,        \* TRUE while the drone holds a valid drop lease
    override       \* privileged incident-commander override engaged

vars == << phase, releaseCount, leased, override >>

Init ==
    /\ phase = "armed"
    /\ releaseCount = 0
    /\ leased = FALSE
    /\ override = FALSE

\* The drone acquires a drop lease while still armed.
Acquire ==
    /\ phase = "armed"
    /\ ~leased
    /\ leased' = TRUE
    /\ UNCHANGED << phase, releaseCount, override >>

\* Perform the single irreversible retardant drop; requires a held lease.
Release ==
    /\ phase = "armed"
    /\ leased
    /\ phase' = "released"
    /\ releaseCount' = releaseCount + 1
    /\ UNCHANGED << leased, override >>

\* The drop lease expires on its own.
Expire ==
    /\ leased
    /\ leased' = FALSE
    /\ UNCHANGED << phase, releaseCount, override >>

\* Under override, the commander may revoke a lease before any drop happens.
AdminRevoke ==
    /\ override
    /\ leased
    /\ leased' = FALSE
    /\ UNCHANGED << phase, releaseCount, override >>

\* Toggle the privileged override (always available).
ToggleOverride ==
    /\ override' = ~override
    /\ UNCHANGED << phase, releaseCount, leased >>

Next ==
    \/ Acquire
    \/ Release
    \/ Expire
    \/ AdminRevoke
    \/ ToggleOverride

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ phase \in {"armed", "released"}
    /\ releaseCount \in 0..2
    /\ leased \in BOOLEAN
    /\ override \in BOOLEAN

\* The irreversible retardant drop happens at most once: the release counter
\* is exactly one once released and zero while still armed, so no lease churn
\* or override can ever cause a second drop.
DropOnce == releaseCount = (IF phase = "released" THEN 1 ELSE 0)

===========================================================================