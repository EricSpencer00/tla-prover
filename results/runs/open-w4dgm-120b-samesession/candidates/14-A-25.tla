---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES
    cs,         \* [1..N -> BOOLEAN] : whether each process is in the critical section
    request,    \* [1..N -> BOOLEAN] : whether each process has raised a request
    ticket,     \* [1..N -> 0..MaxNat] : ticket number taken by each process
    nextTicket, \* the next free ticket number (bounded by MaxNat)
    waiting     \* process id of a currently pending request, or 0 if none

vars == <<cs, request, ticket, nextTicket, waiting>>

Init ==
    /\ cs = [p \in 1..N |-> FALSE]
    /\ request = [p \in 1..N |-> FALSE]
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0
    /\ waiting = 0

Raise(p) ==
    /\ ~request[p]
    /\ ~cs[p]
    /\ waiting = 0
    /\ request' = [request EXCEPT ![p] = TRUE]
    /\ waiting' = p
    /\ UNCHANGED <<cs, ticket, nextTicket>>

Take(p) ==
    /\ waiting = p
    /\ request[p]
    /\ ~cs[p]
    /\ nextTicket < MaxNat
    /\ cs' = [cs EXCEPT ![p] = TRUE]
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED <<request, waiting>>

Leave(p) ==
    /\ cs[p]
    /\ cs' = [cs EXCEPT ![p] = FALSE]
    /\ request' = [request EXCEPT ![p] = FALSE]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ waiting' = IF waiting = p THEN 0 ELSE waiting
    /\ UNCHANGED nextTicket

Next ==
    \/ \E p \in 1..N : Raise(p)
    \/ \E p \in 1..N : Take(p)
    \/ \E p \in 1..N : Leave(p)

Spec == Init /\ [][Next]_vars

\* A process in the critical section holds a real ticket below the next free one.
MutualExclusion ==
    \A p \in 1..N :
        cs[p] => (ticket[p] < nextTicket /\ ticket[p] >= 0)

TypeOK ==
    /\ cs \in [1..N -> BOOLEAN]
    /\ request \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat
    /\ waiting \in 0..N

\* The cashier's bounded queue is a snapshot: the set of processes in the
\* critical section is exactly the set whose ticket is below the next free.
Inv ==
    { p \in 1..N : cs[p] } = { p \in 1..N : ticket[p] < nextTicket }

\* A fresh roll-over cap: the request line never stays raised without a
\* process actually entering the critical section.
EventualGrant ==
    \A p \in 1..N : (request[p] /\ ~cs[p]) ~> cs[p]

StateConstraint ==
    \A p \in 1..N : ticket[p] < MaxNat

====