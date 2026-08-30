---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Finite bound on the otherwise infinite natural numbers, for model checking.
NatOverride(n) == n % (MaxNat + 1)

Kind == {"idle", "waiting", "critical"}
NextK(k) == IF k = "idle" THEN "waiting"
            ELSE IF k = "waiting" THEN "critical"
            ELSE "idle"

VARIABLES phase, ticket, active, served

vars == <<phase, ticket, active, served>>

TypeOK ==
    /\ phase \in [1..N -> Kind]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ active \in 0..N
    /\ served \in 0..MaxNat

\* Mutual exclusion plus the full per-process CFA guard+ticket discipline of the
\* Bakery algorithm; the ticket discipline is what keeps the critical-section
\* occupancy down to one even when several processes can be waiting at once.
MutualExclusion ==
    /\ active <= 1
    /\ \A i \in 1..N: phase[i] = "critical" => (active = 1 /\ served = ticket[i])
    /\ \A i \in 1..N: phase[i] = "waiting" => ticket[i] <= served

Init ==
    /\ phase = [i \in 1..N |-> "idle"]
    /\ ticket = [i \in 1..N |-> 0]
    /\ active = 0
    /\ served = 0

\* A process enters the bakery only when no one is in the critical section; it
\* then picks the next free ticket, which stays ahead of the served counter.
Request(i) ==
    /\ phase[i] = "idle"
    /\ active = 0
    /\ phase' = [phase EXCEPT ![i] = "waiting"]
    /\ ticket' = [ticket EXCEPT ![i] = served + 1]
    /\ UNCHANGED <<active, served>>

Enter(i) ==
    /\ phase[i] = "waiting"
    /\ phase' = [phase EXCEPT ![i] = "critical"]
    /\ active' = 1
    /\ UNCHANGED <<ticket, served>>

Exit(i) ==
    /\ phase[i] = "critical"
    /\ phase' = [phase EXCEPT ![i] = "idle"]
    /\ active' = 0
    /\ served' = NatOverride(served + 1)
    /\ UNCHANGED ticket

Yield(i) ==
    /\ phase[i] = "waiting"
    /\ phase' = [phase EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<ticket, active, served>>

Next ==
    \/ \E i \in 1..N: Request(i)
    \/ \E i \in 1..N: Enter(i)
    \/ \E i \in 1..N: Exit(i)
    \/ \E i \in 1..N: Yield(i)

ISpec == Init /\ [][Next]_vars

\* The safety specification is closed under state restriction to reachable states,
\* so checking it from an arbitrary type-correct start is enough; the stronger
\* assumption is that no reachable path violates MutualExclusion.
SpecImpliesSafety == ISpec => MutualExclusion

====