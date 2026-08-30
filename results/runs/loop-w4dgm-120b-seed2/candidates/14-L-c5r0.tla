---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES phase, ticket, observed, admin, inbox

vars == <<phase, ticket, observed, admin, inbox>>

\* The two-phase protocol: observed is the ticket a process read; phase[t] is
\* whether it has committed its acquisition of the single critical section.
TypeOK ==
  /\ phase \in [1..N -> {"idle", "prepared", "critical", "done"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ observed \in [1..N -> 0..MaxNat]
  /\ admin \in BOOLEAN
  /\ inbox \subseteq (1..N) \X (0..MaxNat)

Init ==
  /\ phase = [t \in 1..N |-> "idle"]
  /\ ticket = [t \in 1..N |-> 0]
  /\ observed = [t \in 1..N |-> 0]
  /\ admin = FALSE
  /\ inbox = {}

Read(t) ==
  /\ phase[t] = "idle"
  /\ observed' = [observed EXCEPT ![t] = ticket[t]]
  /\ phase' = [phase EXCEPT ![t] = "prepared"]
  /\ UNCHANGED <<ticket, admin, inbox>>

\* The message is stamped with the observed ticket; it lands in the unordered
\* inbox and may be delivered in any order, modelling network reordering.
SendPrepare(t) ==
  /\ phase[t] = "prepared"
  /\ [t |-> observed[t]] \notin inbox
  /\ inbox' = inbox \cup {[t |-> observed[t]]}
  /\ UNCHANGED <<phase, ticket, observed, admin>>

\* Delivery re-checks the ticket; because the inbox is a set, deliveries may
\* be reordered and a message prepared against an old ticket lands late.
Deliver(m) ==
  /\ m \in inbox
  /\ inbox' = inbox \ {m}
  /\ IF m[2] = ticket[m[1]]
       THEN /\ ticket' = [ticket EXCEPT ![m[1]] = @ + 1]
            /\ phase' = [phase EXCEPT ![m[1]] = "critical"]
       ELSE /\ phase' = [phase EXCEPT ![m[1]] = "idle"]
            /\ UNCHANGED ticket
  /\ UNCHANGED <<observed, admin>>

AdminBreakIn(t) ==
  /\ ~admin
  /\ admin' = TRUE
  /\ phase' = [phase EXCEPT ![t] = "critical"]
  /\ ticket' = [ticket EXCEPT ![t] = @ + 1]
  /\ observed' = [observed EXCEPT ![t] = ticket[t] + 1]
  /\ UNCHANGED inbox

Exit(t) ==
  /\ phase[t] = "critical"
  /\ phase' = [phase EXCEPT ![t] = "done"]
  /\ UNCHANGED <<ticket, observed, admin, inbox>>

AdminRelease(t) ==
  /\ phase[t] = "done"
  /\ admin' = FALSE
  /\ phase' = [phase EXCEPT ![t] = "idle"]
  /\ UNCHANGED <<ticket, observed, inbox>>

Next ==
  \/ \E t \in 1..N : Read(t)
  \/ \E t \in 1..N : SendPrepare(t)
  \/ \E m \in (1..N) \X (0..MaxNat) : Deliver(m)
  \/ \E t \in 1..N : AdminBreakIn(t)
  \/ \E t \in 1..N : Exit(t)
  \/ \E t \in 1..N : AdminRelease(t)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: the critical-section predicate is exactly one process.
MutualExclusion ==
  Cardinality({t \in 1..N : phase[t] = "critical"}) <= 1

\* Safety: a prepared process's observed ticket still matches its own.
NoLostUpdates == \A t \in 1..N : (phase[t] = "prepared") => (observed[t] = ticket[t])

\* The full set of invariants carried over from the Boulanger spec.
Inv == MutualExclusion /\ NoLostUpdates

\* State constraint: prune every state in which any ticket reaches the maximum,
\* which is the finite bound that keeps this model checkable.
StateConstraint == \A t \in 1..N : ticket[t] < MaxNat

====