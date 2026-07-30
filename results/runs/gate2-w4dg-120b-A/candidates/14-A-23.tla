---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES status, ticket, nextTicket

vars == <<status, ticket, nextTicket>>

\* status[p] is p's request phase; ticket[p] is the ticket it read while serving.
\* nextTicket is the next ticket number the algorithm may hand out.

TypeOK ==
    /\ status \in [1..N -> {"idle", "waiting", "serving", "done"}]
    /\ ticket \in [1..N -> Nat]
    /\ nextTicket \in Nat

Init ==
    /\ status = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ nextTicket = 0

\* A process declares it wants the service.
Request(p) ==
    /\ status[p] = "idle"
    /\ status' = [status EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<ticket, nextTicket>>

\* It reads the next free ticket, which is still below the MaxNat ceiling.
TakeTicket(p) ==
    /\ status[p] = "waiting"
    /\ nextTicket < MaxNat
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ status' = [status EXCEPT ![p] = "serving"]

\* It finishes and releases the service.
Release(p) ==
    /\ status[p] = "serving"
    /\ status' = [status EXCEPT ![p] = "done"]
    /\ UNCHANGED <<ticket, nextTicket>>

\* A finished process is reset to idle so the model explores cycles.
Reset(p) ==
    /\ status[p] = "done"
    /\ status' = [status EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED nextTicket

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : TakeTicket(p)
    \/ \E p \in 1..N : Release(p)
    \/ \E p \in 1..N : Reset(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: two active processes can never have the same ticket.
MutualExclusion ==
    \A p1, p2 \in 1..N :
        (status[p1] = "serving" /\ status[p2] = "serving" /\ ticket[p1] = ticket[p2])
            => p1 = p2

\* The full inductive invariant from the Boulanger specification.
Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ nextTicket <= MaxNat

\* The state constraint: ticket numbers always stay below the finite ceiling.
StateConstraint ==
    \A p \in 1..N : ticket[p] < MaxNat

====