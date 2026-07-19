-------------------------- MODULE W4Od0m6p0t4 --------------------------
EXTENDS Naturals

CONSTANTS Teams, MaxClock, LeaseDur

VARIABLES
    clock,      \* shared clock
    held,       \* held[t] : TRUE iff team t currently holds a lease
    expiry,     \* expiry[t] : clock time the team's lease lapses
    active,     \* set of currently-staffed teams (capacity, changes at runtime)
    inService   \* TRUE iff the robot is in service

vars == << clock, held, expiry, active, inService >>

TypeOK ==
    /\ clock \in 0..MaxClock
    /\ held \in [Teams -> BOOLEAN]
    /\ expiry \in [Teams -> 0..(MaxClock + LeaseDur)]
    /\ active \subseteq Teams
    /\ inService \in BOOLEAN

Init ==
    /\ clock = 0
    /\ held = [t \in Teams |-> FALSE]
    /\ expiry = [t \in Teams |-> 0]
    /\ active = Teams
    /\ inService = TRUE

Valid(t) == held[t] /\ (expiry[t] > clock)

\* Grant the robot to an active team when in service and unheld.
Grant(t) ==
    /\ inService
    /\ t \in active
    /\ ~held[t]
    /\ \A q \in Teams : ~Valid(q)
    /\ held' = [held EXCEPT ![t] = TRUE]
    /\ expiry' = [expiry EXCEPT ![t] = clock + LeaseDur]
    /\ UNCHANGED << clock, active, inService >>

Release(t) ==
    /\ held[t]
    /\ held' = [held EXCEPT ![t] = FALSE]
    /\ UNCHANGED << clock, expiry, active, inService >>

DropExpired(t) ==
    /\ held[t]
    /\ expiry[t] <= clock
    /\ held' = [held EXCEPT ![t] = FALSE]
    /\ UNCHANGED << clock, expiry, active, inService >>

Tick ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    /\ UNCHANGED << held, expiry, active, inService >>

\* Staffing capacity changes at runtime.
Activate(t) ==
    /\ t \notin active
    /\ active' = active \cup {t}
    /\ UNCHANGED << clock, held, expiry, inService >>

StandDown(t) ==
    /\ t \in active
    /\ ~held[t]
    /\ active' = active \ {t}
    /\ UNCHANGED << clock, held, expiry, inService >>

\* Maintenance forcibly clears any hold.
GoOutOfService ==
    /\ inService
    /\ inService' = FALSE
    /\ held' = [t \in Teams |-> FALSE]
    /\ UNCHANGED << clock, expiry, active >>

GoInService ==
    /\ ~inService
    /\ inService' = TRUE
    /\ UNCHANGED << clock, held, expiry, active >>

Next ==
    \/ \E t \in Teams : Grant(t)
    \/ \E t \in Teams : Release(t)
    \/ \E t \in Teams : DropExpired(t)
    \/ Tick
    \/ \E t \in Teams : Activate(t)
    \/ \E t \in Teams : StandDown(t)
    \/ GoOutOfService
    \/ GoInService

Spec == Init /\ [][Next]_vars

\* Mutual exclusion of the single robot: one valid holder at most, and none
\* while out of service.
RobotExclusion ==
    /\ \A p, q \in Teams : (Valid(p) /\ Valid(q)) => (p = q)
    /\ (~inService => \A t \in Teams : ~held[t])

=============================================================================
