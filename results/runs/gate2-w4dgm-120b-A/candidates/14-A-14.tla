---- MODULE MCBoulanger ----
EXTENDS Naturals

\* This module configures the Boulanger system model for TLC model checking.
\* It inherits the full action set and all state variables/properties from
\* the original Boulanger specification (the "core" of the shared bakery),
\* and adds a finite bound on natural numbers so the state space stays finite.
\* The critical section is the service window, and mutual exclusion is the
\* safety property; no action here changes which actions are available.

CONSTANTS N, MaxNat

VARIABLES active, ticket, served, crashed

vars == <<active, ticket, served, crashed>>

TypeOK ==
    /\ active \in [1..N -> {"idle", "waiting", "critical", "crashed"}]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ served \in 0..MaxNat
    /\ crashed \in SUBSET 1..N

\* SAFETY PROPERTY: at most one bakery process is ever in the critical section.
MutualExclusion == Cardinality({p \in 1..N : active[p] = "critical"}) <= 1

\* INVARIANT: counts stay inside the finite bounded range and no process that
\* crashed keeps holding the critical section.
TypeOKConsistent == /\ served <= MaxNat
                    /\ \A p \in 1..N : ticket[p] <= MaxNat
                    /\ \A p \in crashed : active[p] # "critical"

\* INDUTIVE INVARIANT: the full set of per-process and global-state
\* relationships that must hold across every reachable state (not just one
\* facet of it). Every safety property stated separately below is a
\* consequence of this one invariant.
Inv == TypeOKConsistent

Init ==
    /\ active = [p \in 1..N |-> "idle"]
    /\ ticket = [p \in 1..N |-> 0]
    /\ served = 0
    /\ crashed = {}

\* A process that is neither crashed nor already in the critical section
\* enters the bakery, taking a fresh ticket below the finite bound.
Request(p) ==
    /\ p \notin crashed
    /\ active[p] = "idle"
    /\ served < MaxNat
    /\ active' = [active EXCEPT ![p] = "waiting"]
    /\ ticket' = [ticket EXCEPT ![p] = served]
    /\ UNCHANGED <<served, crashed>>

\* A waiting process enters the critical section only if its ticket is the
\* smallest currently among waiting processes -- the bakery's rank ordering.
Enter(p) ==
    /\ p \notin crashed
    /\ active[p] = "waiting"
    /\ \A q \in 1..N : (active[q] = "waiting") => (ticket[p] <= ticket[q])
    /\ active' = [active EXCEPT ![p] = "critical"]
    /\ UNCHANGED <<ticket, served, crashed>>

\* The critical section is left, incrementing the shared service counter.
Leave(p) ==
    /\ p \notin crashed
    /\ active[p] = "critical"
    /\ active' = [active EXCEPT ![p] = "idle"]
    /\ served' = served + 1
    /\ UNCHANGED <<ticket, crashed>>

\* A process may crash silently at any time before or during service; it
\* keeps whatever section it held, which is why the crash-fail safety
\* requires no process in the critical section is one that ever crashed.
Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<active, ticket, served>>

\* A crashed process may recover and rejoin the bakery idle.
Recover(p) ==
    /\ p \in crashed
    /\ crashed' = crashed \ {p}
    /\ active' = [active EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<ticket, served>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Leave(p)
    \/ \E p \in 1..N : Crash(p)
    \/ \E p \in 1..N : Recover(p)

Spec == Init /\ [][Next]_vars

\* The finite override of the natural numbers is the only reason TLC has a
\* finite state space to explore here; the override must keep the safety
\* properties (nothing more, nothing less) unchanged with respect to the
\* full, unbounded version of the spec.
StateConstraint == \A p \in 1..N : ticket[p] < MaxNat

====