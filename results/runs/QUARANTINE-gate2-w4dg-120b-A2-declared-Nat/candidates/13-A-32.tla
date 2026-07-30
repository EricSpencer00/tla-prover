---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES ticket, number, entered

TypeOK ==
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ number \in 0..MaxNat
    /\ entered \subseteq (1..N)

Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ number = 0
    /\ entered = {}

Idle(i) ==
    /\ ticket[i] = 0
    /\ number < MaxNat
    /\ ticket' = [ticket EXCEPT ![i] = number + 1]
    /\ number' = number + 1
    /\ UNCHANGED entered

FastLane(i) ==
    /\ ticket[i] = 0
    /\ number = MaxNat
    /\ ticket' = [ticket EXCEPT ![i] = 1]
    /\ UNCHANGED <<number, entered>>

Enter(i) ==
    /\ ticket[i] > 0
    /\ entered = {}
    /\ entered' = {i}
    /\ UNCHANGED <<ticket, number>>

FastExit(i) ==
    /\ entered = {i}
    /\ entered' = {}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ number' = 0

SlowExit(i) ==
    /\ entered = {i}
    /\ entered' = {}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED number

Next ==
    \/ \E i \in 1..N : Idle(i)
    \/ \E i \in 1..N : FastLane(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : FastExit(i)
    \/ \E i \in 1..N : SlowExit(i)

MutualExclusion ==
    \A i \in entered, j \in entered : i = j

Inv == TypeOK /\ MutualExclusion

ISpec == Init /\ [][Next]_<<ticket, number, entered>>

NatOverride == Nat
====