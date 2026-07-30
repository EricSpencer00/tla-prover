---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The Boulanger mutual exclusion algorithm, but with Nat confined to a bounded range.
\* All invariants and actions are inherited unchanged; the twist is the state
\* constraint below, which prunes states whose tickets reach the configured bound.

VARIABLES phase, ticket, applied, appliedTo

vars == <<phase, ticket, applied, appliedTo>>

TypeOK ==
  /\ phase \in [1..N -> {"idle", "applying", "critical"}]
  /\ ticket \in [1..N -> 0..(MaxNat - 1)]
  /\ applied \in [1..N -> BOOLEAN]
  /\ appliedTo \in [1..N -> 0..N]

Init ==
  /\ phase = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ applied = [p \in 1..N |-> FALSE]
  /\ appliedTo = [p \in 1..N |-> 0]

\* A free process takes a ticket and begins the request phase.
Apply(p) ==
  /\ phase[p] = "idle"
  /\ phase' = [phase EXCEPT ![p] = "applying"]
  /\ ticket' = [ticket EXCEPT ![p] = (ticket[p] + 1) % MaxNat]
  /\ applied' = [applied EXCEPT ![p] = TRUE]
  /\ appliedTo' = [appliedTo EXCEPT ![p] = 0]

\* A process enters the critical section once its ticket is dominant among the
\* processes currently applying.
Enter(p) ==
  /\ phase[p] = "applying"
  /\ \A q \in 1..N : phase[q] # "applying" => ticket[p] > ticket[q]
  /\ phase' = [phase EXCEPT ![p] = "critical"]
  /\ applied' = [applied EXCEPT ![p] = FALSE]
  /\ appliedTo' = [appliedTo EXCEPT ![p] = 0]
  /\ UNCHANGED ticket

\* A process in the critical section leaves it and resets its ticket.
Release(p) ==
  /\ phase[p] = "critical"
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ applied' = [applied EXCEPT ![p] = FALSE]
  /\ appliedTo' = [appliedTo EXCEPT ![p] = 0]

Cancel(p) ==
  /\ phase[p] = "applying"
  /\ ~applied[p]
  /\ appliedTo[p] <= MaxNat
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ applied' = [applied EXCEPT ![p] = FALSE]
  /\ UNCHANGED appliedTo

Next ==
  \/ \E p \in 1..N : Apply(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Release(p)
  \/ \E p \in 1..N : Cancel(p)

Spec == Init /\ [][Next]_vars

StateConstraint == \A p \in 1..N : ticket[p] < MaxNat

MutualExclusion ==
  \A p, q \in 1..N :
    (phase[p] = "critical" /\ phase[q] = "critical") => (p = q)

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A p \in 1..N : phase[p] = "critical" => applied[p] = FALSE

====