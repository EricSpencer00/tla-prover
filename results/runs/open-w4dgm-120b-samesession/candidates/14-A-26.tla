---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, nextTicket, crashed, spins

vars == <<inCS, ticket, nextTicket, crashed, spins>>

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ crashed \subseteq 1..N
    /\ spins \in 0..MaxNat

Init ==
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0
    /\ crashed = {}
    /\ spins = 0

Acquire(p) ==
    /\ p \notin crashed
    /\ ~inCS[p]
    /\ \A q \in 1..N : ~inCS[q]
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
    /\ UNCHANGED <<crashed, spins>>

Release(p) ==
    /\ p \notin crashed
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<ticket, nextTicket, crashed, spins>>

Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<inCS, ticket, nextTicket, spins>>

Recover(p) ==
    /\ p \in crashed
    /\ crashed' = crashed \ {p}
    /\ UNCHANGED <<inCS, ticket, nextTicket, spins>>

Spin ==
    /\ spins < MaxNat
    /\ spins' = spins + 1
    /\ UNCHANGED <<inCS, ticket, nextTicket, crashed>>

Next ==
    \/ \E p \in 1..N : Acquire(p)
    \/ \E p \in 1..N : Release(p)
    \/ \E p \in 1..N : Crash(p)
    \/ \E p \in 1..N : Recover(p)
    \/ Spin

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N : inCS[p] => (\A q \in 1..N \ {p} : ~inCS[q])

Inv ==
    /\ \A a, b \in 1..N : (inCS[a] /\ inCS[b]) => a = b
    /\ \A p \in 1..N : inCS[p] => ticket[p] = nextTicket - 1

StateConstraint ==
    \A p \in 1..N : ticket[p] < MaxNat

====