---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES mode, phase, ticket, snap, served, crashed

vars == <<mode phase, ticket, snap, served, crashed>>

Modes == {"idle", "cs"}
Phases == {"idle", "reading", "critical"}
Idle == [m |-> "idle", p |-> 0]

TypeOK ==
    /\ mode \in 0..N
    /\ phase \in [1..N -> Phases]
    /\ ticket \in [1..N -> 0..(MaxNat - 1)]
    /\ snap \in [1..N -> 0..MaxNat]
    /\ served \in 0..N
    /\ crashed \in [1..N -> BOOLEAN]

Init ==
    /\ mode = 0
    /\ phase = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ snap = [p \in 1..N |-> 0]
    /\ served = 0
    /\ crashed = [p \in 1..N |-> FALSE]

Enter(p) ==
    /\ phase[p] = "idle"
    /\ ~crashed[p]
    /\ phase' = [phase EXCEPT ![p] = "reading"]
    /\ snap' = [snap EXCEPT ![p] = mode]
    /\ UNCHANGED <<mode, ticket, served, crashed>>

Win(p) ==
    /\ phase[p] = "reading"
    /\ snap[p] = mode
    /\ mode = 0
    /\ mode' = p
    /\ ticket' = [ticket EXCEPT ![p] = mode]
    /\ phase' = [phase EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<snap, served, crashed>>

Lose(p) ==
    /\ phase[p] = "reading"
    /\ snap[p] # mode
    /\ phase' = [phase EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<mode, ticket, snap, served, crashed>>

Exit(p) ==
    /\ phase[p] = "critical"
    /\ phase' = [phase EXCEPT ![p] = "idle"]
    /\ mode' = 0
    /\ served' = IF served < N THEN served + 1 ELSE served
    /\ UNCHANGED <<ticket, snap, crashed>>

Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ phase' = [phase EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<mode, ticket, snap, served>>

Next ==
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Win(p)
    \/ \E p \in 1..N : Lose(p)
    \/ \E p \in 1..N : Exit(p)
    \/ \E p \in 1..N : Crash(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N :
        (phase[p] = "critical") => (mode = p /\ ticket[p] = mode)

\* The full inductive invariant: no alive critical section and the lock word
\* never runs beyond the bounded ticket range, which is what makes the finite
\* override of the natural numbers safe to explore.
Inv ==
    /\ \A p \in 1..N : (phase[p] = "critical") => (mode = p /\ ~crashed[p])
    /\ mode <= N
    /\ \A p \in 1..N : ticket[p] <= N
    /\ \A p \in 1..N : (crashed[p] => (phase[p] = "idle"))
====