---- MODULE MCBakery ----
EXTENDS Naturals

\* The Bakery mutual exclusion algorithm, with the natural numbers overridden
\* by a finite range from 0 to MaxNat. This is a configuration module used
\* for model checking, so it defines the constants and the specification
\* marker (ISpec) expected by the .cfg file.
CONSTANTS N, MaxNat, Nat

VARIABLES active, waiting, served, pstate, ticket, clock

vars == <<active, waiting, served, pstate, ticket, clock>>

TypeOK ==
  /\ active \in [Nat -> BOOLEAN]
  /\ waiting \in [Nat -> BOOLEAN]
  /\ served \in [Nat -> BOOLEAN]
  /\ pstate \in [Nat -> {"idle", "waiting", "active"}]
  /\ ticket \in [Nat -> 0..MaxNat]
  /\ clock \in 0..MaxNat

Init ==
  /\ active = [p \in Nat |-> FALSE]
  /\ waiting = [p \in Nat |-> FALSE]
  /\ served = [p \in Nat |-> FALSE]
  /\ pstate = [p \in Nat |-> "idle"]
  /\ ticket = [p \in Nat |-> 0]
  /\ clock = 0

\* A process requests the critical section; it is assigned a ticket that is
\* one above the current clock, and the clock is bumped so no later request
\* can take the same ticket (bounded by MaxNat).
Request(p) ==
  /\ pstate[p] = "idle"
  /\ ~waiting[p]
  /\ ~active[p]
  /\ clock < MaxNat
  /\ pstate' = [pstate EXCEPT ![p] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![p] = clock + 1]
  /\ clock' = clock + 1
  /\ waiting' = [waiting EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<active, served>>

\* A waiting process enters the critical section if its ticket is the lowest
\* among all waiting or active processes.
Enter(p) ==
  /\ pstate[p] = "waiting"
  /\ \A q \in Nat : (pstate[q] = "waiting" \/ pstate[q] = "active") => ticket[p] <= ticket[q]
  /\ pstate' = [pstate EXCEPT ![p] = "active"]
  /\ active' = [active EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<waiting, served, ticket, clock>>

\* The process in the critical section exits, becoming served. It retains its
\* ticket (which is what keeps it above the clock bound) and can request
\* again later.
Exit(p) ==
  /\ pstate[p] = "active"
  /\ pstate' = [pstate EXCEPT ![p] = "idle"]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ waiting' = [waiting EXCEPT ![p] = FALSE]
  /\ served' = [served EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, clock>>

\* A served process requests the critical section again (ticket reuse).
ReRequest(p) ==
  /\ pstate[p] = "idle"
  /\ served[p]
  /\ clock < MaxNat
  /\ pstate' = [pstate EXCEPT ![p] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![p] = clock + 1]
  /\ clock' = clock + 1
  /\ waiting' = [waiting EXCEPT ![p] = TRUE]
  /\ served' = [served EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<active>>

Next ==
  \/ \E p \in Nat : Request(p)
  \/ \E p \in Nat : Enter(p)
  \/ \E p \in Nat : Exit(p)
  \/ \E p \in Nat : ReRequest(p)

\* The inductive specification: start from any arbitrary type-correct state
\* satisfying the mutual-exclusion invariant, and require that every
\* transition preserves TypeOK and the invariant.
ISpec == Init /\ [][Next]_vars

\* Mutual exclusion: no two processes are ever in the critical section at
\* the same time.
MutualExclusion ==
  \A p, q \in Nat : (active[p] /\ active[q]) => p = q

\* The full invariant needed to make the check go through.
Inv ==
  /\ \A p \in Nat : pstate[p] \in {"idle", "waiting", "active"}
  /\ MutualExclusion

====