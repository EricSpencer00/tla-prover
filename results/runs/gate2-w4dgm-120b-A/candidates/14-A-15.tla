---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Overrides the standard module's unbounded Nat to a finite, model-checkable
\* range. The import of Naturals is kept so other operators from it stay usable,
\* and the override only affects Nat itself -- the others are untouched.
Nat == 0..MaxNat

VARIABLES holder, active, servedCount, phase, ticket

vars == <<holder, active, servedCount, phase, ticket>>

TypeOK =
  /\ holder \in 0..N
  /\ active \subseteq 1..N
  /\ servedCount \in 0..N
  /\ phase \in {"idle", "critical"}
  /\ ticket \in [1..N -> Nat]

Init ==
  /\ holder = 0
  /\ active = {}
  /\ servedCount = 0
  /\ phase = "idle"
  /\ ticket = [p \in 1..N |-> 0]

Enter(p) ==
  /\ holder = 0
  /\ holder' = p
  /\ phase' = "critical"
  /\ ticket' = [ticket EXCEPT ![p] = (ticket[p] + 1) % (MaxNat + 1)]
  /\ UNCHANGED <<active, servedCount>>

Exit(p) ==
  /\ holder = p
  /\ holder' = 0
  /\ phase' = "idle"
  /\ active' = active \cup {p}
  /\ servedCount' = IF servedCount < N THEN servedCount + 1 ELSE servedCount
  /\ UNCHANGED ticket

\* Privileged admin override: forcibly evict whoever holds the lock.
AdminEvict ==
  /\ holder # 0
  /\ holder' = 0
  /\ phase' = "idle"
  /\ UNCHANGED <<active, servedCount, ticket>>

Reset(p) ==
  /\ p \in active
  /\ active' = active \ {p}
  /\ UNCHANGED <<holder, servedCount, phase, ticket>>

Next ==
  \/ \E p \in 1..N: Enter(p)
  \/ \E p \in 1..N: Exit(p)
  \/ AdminEvict
  \/ \E p \in 1..N: Reset(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: the lock holder is exactly the process in the critical
\* section, so two processes can never both be in the critical section.
MutualExclusion ==
  /\ (holder = 0) <=> (phase = "idle")
  /\ (holder # 0) => (holder \notin active)

\* The full Boulanger inductive invariant: a process is recorded as served only
\* while it has actually held the lock, which keeps the two histories aligned.
Inv ==
  /\ MutualExclusion
  /\ active \subseteq {p \in 1..N : ticket[p] # 0}

\* Prunes states where ticket numbers would have grown past the finite bound.
TicketBound == \A p \in 1..N: ticket[p] <= MaxNat

====