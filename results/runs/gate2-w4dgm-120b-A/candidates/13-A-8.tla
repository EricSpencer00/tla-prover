---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* A process is idle, in the bakery choosing a ticket, or in the critical section holding its ticket.
VARIABLES stage, ticket, choosing, served

vars == <<stage, ticket, choosing, served>>

TypeOK ==
    /\ stage \in [0..N-1] -> {"idle", "waiting", "cs"}
    /\ ticket \in [0..N-1 -> 0..MaxNat]
    /\ choosing \in [0..N-1 -> BOOLEAN]
    /\ served \in 0..N

Init ==
    /\ stage = [i \in 0..N-1 |-> "idle"]
    /\ ticket = [i \in 0..N-1 |-> 0]
    /\ choosing = [i \in 0..N-1 |-> FALSE]
    /\ served = 0

\* A process that is idle enters the bakery to draw a ticket, up to the bounded limit.
Choose(i) ==
    /\ stage[i] = "idle"
    /\ served < N
    /\ stage' = [stage EXCEPT ![i] = "waiting"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, served>>

\* The bakery hands the choosing process the lowest free ticket number, bounded by MaxNat.
TicketAssigned(i) ==
    /\ stage[i] = "waiting"
    /\ choosing[i] = TRUE
    /\ \E t \in 1..MaxNat :
        /\ \A k \in 0..N-1 : (stage[k] = "cs") => ticket[k] # t
        /\ ticket' = [ticket EXCEPT ![i] = t]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<stage, served>>

\* A waiting process enters the critical section once its ticket is the lowest among all
\* processes still waiting, giving strict priority to lower tickets.
Enter(i) ==
    /\ stage[i] = "waiting"
    /\ ~choosing[i]
    /\ \A k \in 0..N-1 : (stage[k] = "waiting") => ticket[i] <= ticket[k]
    /\ stage' = [stage EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, choosing, served>>

\* A process in the critical section leaves, becoming idle and releasing its ticket.
Leave(i) ==
    /\ stage[i] = "cs"
    /\ stage' = [stage EXCEPT ![i] = "idle"]
    /\ served' = IF served < N THEN served + 1 ELSE served
    /\ UNCHANGED <<ticket, choosing>>

Next ==
    \/ \E i \in 0..N-1 : Choose(i)
    \/ \E i \in 0..N-1 : TicketAssigned(i)
    \/ \E i \in 0..N-1 : Enter(i)
    \/ \E i \in 0..N-1 : Leave(i)

\* Strong fairness on every process's own three steps keeps the bakery from stalling on any one
\* process forever, and lets every process that joins eventually leave the critical section.
SpecAction == Next
Fairness ==
    /\ \A i \in 0..N-1 : SF_vars(Choose(i))
    /\ \A i \in 0..N-1 : WF_vars(TicketAssigned(i))
    /\ \A i \in 0..N-1 : SF_vars(Enter(i))
    /\ \A i \in 0..N-1 : WF_vars(Leave(i))

\* Mutual exclusion expressed as a non-decreasing ticket order over the processes currently in the
\* critical section: no two critical processes can hold tickets that contradict the bakery ordering.
MutualExclusion ==
    \A i, j \in 0..N-1 :
        (stage[i] = "cs" /\ stage[j] = "cs") => ticket[i] <= ticket[j]

\* Safety invariant from the Bakery specification, preserved across all transitions.
Inv ==
    /\ (served <= N)
    /\ \A i \in 0..N-1 : (stage[i] = "waiting") => ticket[i] >= 1
    /\ \A i, j \in 0..N-1 :
        (stage[i] = "cs" /\ stage[j] = "cs") => ticket[i] <= ticket[j]

ISpec == SpecAction /\ Fairness

====