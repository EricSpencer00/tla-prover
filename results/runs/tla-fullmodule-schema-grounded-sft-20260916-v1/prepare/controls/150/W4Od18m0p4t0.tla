---- MODULE W4Od18m0p4t0 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Passes, Hubs, Cap, MaxRev, NoHub

ASSUME NoHub \notin Hubs

VARIABLES pass, live, rev, dark

vars == <<pass, live, rev, dark>>

Typing ==
    /\ pass \in [Passes -> [state : {"asked", "reading", "granted", "refused",
                                     "expired"},
                            base : 0..MaxRev, hub : Hubs \cup {NoHub}]]
    /\ live \subseteq Passes
    /\ rev \in 0..MaxRev
    /\ dark \subseteq Hubs

Init ==
    /\ pass = [p \in Passes |-> [state |-> "asked", base |-> 0, hub |-> NoHub]]
    /\ live = {}
    /\ rev = 0
    /\ dark = {}

\* A hub reads how many guest passes are live and the revision stamped on that
\* count, then goes away to check the request against the household's rules.
Read(p, h) ==
    /\ pass[p].state = "asked"
    /\ h \notin dark
    /\ pass' = [pass EXCEPT ![p] = [state |-> "reading", base |-> rev, hub |-> h]]
    /\ UNCHANGED <<live, rev, dark>>

\* Granting a pass only lands while the revision the hub read is still the one
\* on the count, and only while there is room under the household's limit.
Grant(p) ==
    /\ pass[p].state = "reading"
    /\ pass[p].hub \notin dark
    /\ pass[p].base = rev
    /\ Cardinality(live) < Cap
    /\ rev < MaxRev
    /\ live' = live \cup {p}
    /\ rev' = rev + 1
    /\ pass' = [pass EXCEPT ![p].state = "granted"]
    /\ UNCHANGED dark

\* A request whose read has gone stale, whose hub has dropped off, or that
\* arrives with the household already at its limit, is refused outright.
Refuse(p) ==
    /\ pass[p].state = "reading"
    /\ \/ pass[p].base # rev
       \/ pass[p].hub \in dark
       \/ Cardinality(live) = Cap
       \/ rev = MaxRev
    /\ pass' = [pass EXCEPT ![p].state = "refused"]
    /\ UNCHANGED <<live, rev, dark>>

\* A live pass is handed back when the guest leaves, freeing a slot.
Expire(p) ==
    /\ p \in live
    /\ rev < MaxRev
    /\ live' = live \ {p}
    /\ rev' = rev + 1
    /\ pass' = [pass EXCEPT ![p].state = "expired"]
    /\ UNCHANGED dark

\* One hub may drop off the home mesh without saying so.
GoDark(h) ==
    /\ dark = {}
    /\ Cardinality(Hubs) > 1
    /\ dark' = {h}
    /\ UNCHANGED <<pass, live, rev>>

Quiet ==
    /\ \A p \in Passes : pass[p].state \in {"granted", "refused", "expired"}
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Passes, h \in Hubs : Read(p, h)
    \/ \E p \in Passes : Grant(p) \/ Refuse(p) \/ Expire(p)
    \/ \E h \in Hubs : GoDark(h)
    \/ Quiet

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Passes, h \in Hubs : Read(p, h))
    /\ WF_vars(\E p \in Passes : Grant(p))
    /\ WF_vars(\E p \in Passes : Refuse(p))

\* Whenever a guest pass is live, the household is holding no more live passes
\* than its limit allows, however many hubs raced each other to grant one.
PassCapacityRespected ==
    \A p \in Passes :
        (pass[p].state = "granted") => (Cardinality(live) <= Cap)

EveryRequestEventuallyAnswered ==
    \A p \in Passes :
        (pass[p].state = "asked") ~>
            (pass[p].state = "granted" \/ pass[p].state = "refused")

====