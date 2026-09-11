---- MODULE W4Od16m6p0t1 ----
EXTENDS Naturals

CONSTANTS Techs, Scripts, Span, NoTech, NoScript

VARIABLES running, lease, bus, filled, job

Vars == <<running, lease, bus, filled, job>>

Live(t) == lease.holder = t /\ lease.ticks > 0

TypeOK ==
    ( (running \subseteq Techs /\ bus \subseteq Techs)
     /\  (lease \in [holder: {NoTech} \union Techs, ticks: 0..Span])
     /\  (filled \subseteq Scripts)
     /\  (job \in [Techs -> {NoScript} \union Scripts]))

Init ==
    ( (running = {} /\ bus = {} /\ filled = {})
     /\  (lease = [holder |-> NoTech, ticks |-> 0])
     /\  (job = [t \in Techs |-> NoScript]))

\* Nothing may be running on the arm when the lease changes hands.
Grant(t, s) ==
    ( ((lease.holder = NoTech \/ lease.ticks = 0))
     /\  (running = {} /\ job[t] = NoScript /\ s \notin filled)
     /\  (lease' = [holder |-> t, ticks |-> Span])
     /\  (bus' = bus \union {t})
     /\  (job' = [job EXCEPT ![t] = s])
     /\  (UNCHANGED <<running, filled>>))

Tick ==
    ( (lease.ticks > 0)
     /\  (lease' = [lease EXCEPT !.ticks = @ - 1])
     /\  (UNCHANGED <<running, bus, filled, job>>))

\* Acknowledgements arrive out of order, so the holder test is the whole of
\* the protection against a stale one putting a second job on the arm.
StartJob(t) ==
    ( (t \in bus /\ Live(t) /\ job[t] # NoScript)
     /\  (running' = running \union {t})
     /\  (bus' = bus \ {t})
     /\  (UNCHANGED <<lease, filled, job>>))

FinishJob(t) ==
    ( (t \in running /\ job[t] # NoScript)
     /\  (filled' = filled \union {job[t]})
     /\  (job' = [job EXCEPT ![t] = NoScript])
     /\  (running' = running \ {t})
     /\  (lease' = [holder |-> NoTech, ticks |-> 0])
     /\  (UNCHANGED bus))

DropAck(t) ==
    ( (t \in bus /\ lease.holder # t)
     /\  (bus' = bus \ {t})
     /\  (UNCHANGED <<running, lease, filled, job>>))

AbandonJob(t) ==
    ( (job[t] # NoScript /\ t \notin running /\ lease.holder # t)
     /\  (job' = [job EXCEPT ![t] = NoScript])
     /\  (UNCHANGED <<running, lease, bus, filled>>))

StartStep == \E t \in Techs : StartJob(t)

CabinetStep ==
    ( (StartStep)
     \/  (\E t \in Techs : FinishJob(t) \/ DropAck(t) \/ AbandonJob(t))
     \/  (\E t \in Techs, s \in Scripts : Grant(t, s)))

Next == CabinetStep \/ Tick

\* Leases can lapse before an acknowledgement lands, over and over, so the
\* start step needs strong fairness to get a foot in that churn.
Spec ==
    ( (Init /\ [][Next]_Vars)
     /\  (WF_Vars(CabinetStep) /\ SF_Vars(StartStep)))

\* Mutual exclusion of the arm: whoever is running on it is the recorded
\* lease holder, and the record names at most one technician.
ArmHeldByLeaseHolder == \A t \in running : lease.holder = t

\* Progress: every prescription is filled.
AllScriptsFilled == <>(filled = Scripts)
====