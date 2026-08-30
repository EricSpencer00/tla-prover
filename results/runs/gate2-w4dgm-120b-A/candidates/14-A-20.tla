---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

Processes == 1..N
None == 0

VARIABLES ticket, holder, dispensed, beats

vars == <<ticket, holder, dispensed, beats>>

TypeOK ==
    /\ ticket \in [Processes -> 0..MaxNat]
    /\ holder \in Processes \cup {None}
    /\ dispensed \in [Processes -> Nat]
    /\ beats \in 0..MaxNat

Init ==
    /\ ticket = [p \in Processes |-> 0]
    /\ holder = None
    /\ dispensed = [p \in Processes |-> 0]
    /\ beats = 0

TakeTicket(p) ==
    /\ ticket[p] = 0
    /\ \A q \in Processes : ticket[q] # tickets[p] + 1
    /\ ticket' = [ticket EXCEPT ![p] = tickets[p] + 1]
    /\ UNCHANGED <<holder, dispensed, beats>>

Acquire(p) ==
    /\ holder = None
    /\ ticket[p] # 0
    /\ holder' = p
    /\ UNCHANGED <<ticket, dispensed, beats>>

Dispense(p) ==
    /\ holder = p
    /\ dispensed[p] = 0
    /\ dispensed' = [dispensed EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<ticket, holder, beats>>

Release(p) ==
    /\ holder = p
    /\ holder' = None
    /\ UNCHANGED <<ticket, dispensed, beats>>

Tick ==
    /\ beats < MaxNat
    /\ beats' = beats + 1
    /\ UNCHANGED <<ticket, holder, dispensed>>

Next ==
    \/ \E p \in Processes : TakeTicket(p)
    \/ \E p \in Processes : Acquire(p)
    \/ \E p \in Processes : Dispense(p)
    \/ \E p \in Processes : Release(p)
    \/ Tick

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in Processes : (holder = p) => (ticket[p] # 0)

Inv == MutualExclusion /\ TypeOK

StateConstraint == \A p \in Processes : ticket[p] < MaxNat

====