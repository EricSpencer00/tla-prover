---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES ticket, holder, alive, inCS, state, finished, lifetime

vars == <<ticket, holder, alive, inCS, state, finished, lifetime>>

TypeOK ==
    /\ ticket \in 0..(MaxNat - 1)
    /\ holder \in 1..N
    /\ alive \subseteq 1..N
    /\ inCS \subseteq 1..N
    /\ state \in {"idle", "waiting", "inCS"}
    /\ finished \in 0..MaxNat
    /\ lifetime \in 0..MaxNat

Init ==
    /\ ticket = 0
    /\ holder = 1
    /\ alive = 1..N
    /\ inCS = {}
    /\ state = "idle"
    /\ finished = 0
    /\ lifetime = 0

Enter(p) ==
    /\ p \in alive
    /\ p = holder
    /\ state = "idle"
    /\ inCS = {}
    /\ state' = "inCS"
    /\ inCS' = {p}
    /\ UNCHANGED <<ticket, holder, alive, finished, lifetime>>

Exit(p) ==
    /\ state = "inCS"
    /\ p \in inCS
    /\ state' = "idle"
    /\ inCS' = {}
    /\ finished' = IF finished < MaxNat - 1 THEN finished + 1 ELSE finished
    /\ UNCHANGED <<ticket, holder, alive, lifetime>>

Admit ==
    /\ state = "idle"
    /\ inCS = {}
    /\ ticket < MaxNat - 1
    /\ ticket' = ticket + 1
    /\ holder' = IF holder = N THEN 1 ELSE holder + 1
    /\ UNCHANGED <<alive, inCS, state, finished, lifetime>>

Crash(p) ==
    /\ p \in alive
    /\ alive' = alive \ {p}
    /\ inCS' = inCS \ {p}
    /\ UNCHANGED <<ticket, holder, state, finished, lifetime>>

Recover(p) ==
    /\ p \notin alive
    /\ alive' = alive \cup {p}
    /\ UNCHANGED <<ticket, holder, inCS, state, finished, lifetime>>

Age ==
    /\ lifetime < MaxNat - 1
    /\ lifetime' = lifetime + 1
    /\ UNCHANGED <<ticket, holder, alive, inCS, state, finished>>

Next ==
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)
    \/ Admit
    \/ \E p \in 1..N : Crash(p)
    \/ \E p \in 1..N : Recover(p)
    \/ Age

Spec == Init /\ [][Next]_vars

MutualExclusion == \A a, b \in inCS : a = b

Inv == /\ finished = 0
       /\ state = "idle"
       /\ ticket = 0
       /\ inCS = {}

NatOverride == Nat

====