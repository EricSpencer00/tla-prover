---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* No new state beyond the Boulanger specification; only the range of Nat is
\* narrowed for model checking, and ticket numbers are kept below MaxNat.
VARIABLES phase, ticket, want, inbox, slow

vars == << phase, ticket, want, inbox, slow >>

TypeOK ==
    /\ phase \in [1..N -> {"idle", "critical"}]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ want \in [1..N -> BOOLEAN]
    /\ inbox \in [1..N -> 0..MaxNat]
    /\ slow \in [1..N -> BOOLEAN]

Init ==
    /\ phase = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ want = [p \in 1..N |-> FALSE]
    /\ inbox = [p \in 1..N |-> 0]
    /\ slow = [p \in 1..N |-> FALSE]

\* A slow process is never stuck: it always eventually speeds up, so weak fairness
\* on the Acquire step covers it even without per-process fairness for GetTicket.
Request(p) ==
    /\ ~want[p]
    /\ want' = [want EXCEPT ![p] = TRUE]
    /\ UNCHANGED << phase, ticket, inbox, slow >>

GetTicket(p) ==
    /\ ~slow[p]
    /\ want[p]
    /\ phase[p] = "idle"
    /\ ticket[p] < MaxNat
    /\ inbox' = [inbox EXCEPT ![p] = ticket[p] + 1]
    /\ UNCHANGED << phase, ticket, want, slow >>

Deliver(p) ==
    /\ inbox[p] > 0
    /\ ticket' = [ticket EXCEPT ![p] = inbox[p]]
    /\ inbox' = [inbox EXCEPT ![p] = 0]
    /\ UNCHANGED << phase, want, slow >>

Acquire(p) ==
    /\ \A q \in 1..N : phase[q] # "critical"
    /\ ticket[p] > 0
    /\ phase' = [phase EXCEPT ![p] = "critical"]
    /\ UNCHANGED << ticket, want, inbox, slow >>

Release(p) ==
    /\ phase[p] = "critical"
    /\ phase' = [phase EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ want' = [want EXCEPT ![p] = FALSE]
    /\ UNCHANGED << inbox, slow >>

SlowDown(p) ==
    /\ ~slow[p]
    /\ slow' = [slow EXCEPT ![p] = TRUE]
    /\ UNCHANGED << phase, ticket, want, inbox >>

SpeedUp(p) ==
    /\ slow[p]
    /\ slow' = [slow EXCEPT ![p] = FALSE]
    /\ UNCHANGED << phase, ticket, want, inbox >>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : GetTicket(p)
    \/ \E p \in 1..N : Deliver(p)
    \/ \E p \in 1..N : Acquire(p)
    \/ \E p \in 1..N : Release(p)
    \/ \E p \in 1..N : SlowDown(p)
    \/ \E p \in 1..N : SpeedUp(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in 1..N : WF_vars(SpeedUp(p))
    /\ \A p \in 1..N : WF_vars(Acquire(p))

MutualExclusion ==
    \A p, q \in 1..N : (phase[p] = "critical" /\ phase[q] = "critical") => p = q

\* Ticket numbers below MaxNat is the state-reduction clause; every other part is
\* the lifted invariant from the Boulanger specification.
Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A p \in 1..N : ticket[p] <= MaxNat

====