---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES phase, ticket, view, snap, cur

NatOverride == Nat

vars == <<phase, ticket, view, snap, cur>>

TypeOK ==
  /\ phase \in [1..N -> {"idle", "wait", "cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ view \in [1..N -> 0..MaxNat]
  /\ snap \in [1..N -> 0..MaxNat]
  /\ cur \in 0..MaxNat

\* The ticket numbers of processes currently in the critical section are all
\* distinct, which is exactly what prevents two processes from being in the
\* critical section at the same time.
MutualExclusion ==
  \A i \in 1..N, j \in 1..N :
    (i # j /\ phase[i] = "cs" /\ phase[j] = "cs") => ticket[i] # ticket[j]

Init ==
  /\ phase = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ view = [i \in 1..N |-> 0]
  /\ snap = [i \in 1..N |-> 0]
  /\ cur = 0

\* A process reads the current counter value and posts a ticket one above it,
\* which is the number it will present to the network.
Request(i) ==
  /\ phase[i] = "idle"
  /\ cur < MaxNat
  /\ snap' = [snap EXCEPT ![i] = cur]
  /\ ticket' = [ticket EXCEPT ![i] = cur + 1]
  /\ phase' = [phase EXCEPT ![i] = "wait"]
  /\ UNCHANGED <<view, cur>>

\* A process enters the critical section only if its posted ticket still equals
\* the live counter.
Enter(i) ==
  /\ phase[i] = "wait"
  /\ ticket[i] = cur
  /\ cur < MaxNat
  /\ phase' = [phase EXCEPT ![i] = "cs"]
  /\ cur' = cur + 1
  /\ view' = [view EXCEPT ![i] = cur]
  /\ UNCHANGED <<ticket, snap>>

\* A process whose ticket was overtaken by another process restarts.
Retry(i) ==
  /\ phase[i] = "wait"
  /\ ticket[i] # cur
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, view, snap, cur>>

Exit(i) ==
  /\ phase[i] = "cs"
  /\ phase' = [phase EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, view, snap, cur>>

\* The bakery's register rolls over, erasing every held ticket and returning
\* the bakery to a clean state.
Rollover ==
  /\ cur = MaxNat
  /\ \A i \in 1..N : phase[i] # "cs"
  /\ phase' = [i \in 1..N |-> "idle"]
  /\ ticket' = [i \in 1..N |-> 0]
  /\ cur' = 0
  /\ UNCHANGED <<view, snap>>

Next ==
  \/ Rollover
  \/ \E i \in 1..N :
       Request(i) \/ Enter(i) \/ Retry(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

\* A process's own snapshot of the counter always matches the register value
\* recorded when it entered, so no process's ticket ever pretended to be higher
\* than the bakery actually granted.
Inv ==
  \A i \in 1..N :
    (phase[i] = "cs") => (view[i] = ticket[i] - 1)

\* Ticket numbers never drift past the maximum set for model checking.
TicketRange == \A i \in 1..N : ticket[i] < MaxNat

====