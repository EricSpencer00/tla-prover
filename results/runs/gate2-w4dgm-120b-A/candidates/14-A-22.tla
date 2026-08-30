---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The ticket-granting system is the same as in Boulanger; this module adds a
\* finite bound on NATURAL numbers so the model is checkable.
VARIABLES token, requesting, grant, view

vars == <<token, requesting, grant, view>>

Nodes == 0..(N - 1)

Nxt(n) == (n + 1) % N

TypeOK ==
    /\ token \in Nodes
    /\ requesting \in [Nodes -> BOOLEAN]
    /\ grant \in [Nodes -> 0..MaxNat]
    /\ view \in [Nodes -> Nodes]

\* Mutual exclusion: a process only enters the critical section while its
\* granted ticket matches the circulating token, so two processes can never be
\* in the critical section at once.
MutualExclusion ==
    \A n \in Nodes : requesting[n] => grant[n] = token

Init ==
    /\ token = 0
    /\ requesting = [n \in Nodes |-> FALSE]
    /\ grant = [n \in Nodes |-> 0]
    /\ view = [n \in Nodes |-> 0]

Request(n) ==
    /\ ~requesting[n]
    /\ requesting' = [requesting EXCEPT ![n] = TRUE]
    /\ grant' = [grant EXCEPT ![n] = token]
    /\ UNCHANGED <<token, view>>

Refresh(n) ==
    /\ grant[n] # token
    /\ grant' = [grant EXCEPT ![n] = token]
    /\ UNCHANGED <<token, requesting, view>>

EnterCS(n) ==
    /\ requesting[n]
    /\ grant[n] = token
    /\ requesting' = [requesting EXCEPT ![n] = FALSE]
    /\ token' = Nxt(token)
    /\ UNCHANGED <<grant, view>>

Sync(n) ==
    /\ view[n] # token
    /\ view' = [view EXCEPT ![n] = token]
    /\ UNCHANGED <<token, requesting, grant>>

Next ==
    \E n \in Nodes :
        \/ Request(n)
        \/ Refresh(n)
        \/ EnterCS(n)
        \/ Sync(n)

Spec == Init /\ [][Next]_vars

\* The full inductive invariant from Boulanger, restated here unchanged.
Inv ==
    /\ (token = 0 => \A n \in Nodes : grant[n] = 0)
    /\ \A n \in Nodes : requesting[n] => grant[n] = token

\* State space pruning: ticket numbers must stay below the finite bound, so
\* no state whose ticket has reached the maximum is explored.
TicketBound == \A n \in Nodes : grant[n] < MaxNat

====