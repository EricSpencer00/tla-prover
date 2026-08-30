---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES ticket, state, inCS, clock

vars == <<ticket, state, inCS, clock>>

Bump(a) == IF a + 1 >= MaxNat THEN a ELSE a + 1

TypeOK ==
  /\ ticket \in [0 .. MaxNat - 1]
  /\ state \in [0 .. N - 1]
  /\ inCS \in [0 .. N - 1]
  /\ clock \in [0 .. MaxNat - 1]

Init ==
  /\ ticket = 0
  /\ state = [p \in 0 .. N - 1 |-> 0]
  /\ inCS = 0
  /\ clock = 0

Read(p) ==
  /\ state[p] = 0
  /\ state' = [state EXCEPT ![p] = 1]
  /\ UNCHANGED <<ticket, inCS, clock>>

Acquire(p) ==
  /\ state[p] = 1
  /\ inCS = 0
  /\ inCS' = p + 1
  /\ state' = [state EXCEPT ![p] = 2]
  /\ ticket' = Bump(ticket)
  /\ UNCHANGED clock

Release(p) ==
  /\ state[p] = 2
  /\ inCS' = 0
  /\ state' = [state EXCEPT ![p] = 0]
  /\ UNCHANGED <<ticket, clock>>

SlowTick ==
  /\ clock' = Bump(clock)
  /\ UNCHANGED <<ticket, state, inCS>>

Next ==
  \/ \E p \in 0 .. N - 1 : Read(p)
  \/ \E p \in 0 .. N - 1 : Acquire(p)
  \/ \E p \in 0 .. N - 1 : Release(p)
  \/ SlowTick

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 0 .. N - 1 : state[p] = 2 => (inCS = p + 1)

Inv ==
  /\ MutualExclusion
  /\ TypeOK

====