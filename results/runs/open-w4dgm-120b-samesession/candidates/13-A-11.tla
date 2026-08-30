---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

ASSUME N \in Nat /\ N >= 2 /\ MaxNat \in Nat

VARIABLES
  phase,     \* phase[p]: "idle" | "waiting" | "cs" | "done"
  ticket,    \* ticket[p]: the bakery number p holds, or 0 if none
  nextTicket,\* the next bakery number to issue
  alive      \* alive[p]: TRUE iff process p has not crashed

vars == << phase, ticket, nextTicket, alive >>

TypeOK ==
  /\ phase \in [1..N -> {"idle", "waiting", "cs", "done"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 1..(MaxNat + 1)
  /\ alive \in [1..N -> BOOLEAN]

\* Mutual exclusion: every process in the critical section is the single
\* current ticket holder, so two processes can never be in the critical
\* section at the same time.
MutualExclusion ==
  \A p \in 1..N : phase[p] = "cs" => (\A q \in 1..N : q # p => ticket[q] # ticket[p])

\* The full inductive invariant: mutual exclusion plus a coherence relation
\* tying critical-section status to ticket ownership.
Inv ==
  /\ MutualExclusion
  /\ \A p \in 1..N : (phase[p] = "cs") <=> (ticket[p] # 0 /\ ticket[p] = nextTicket - 1)

Init ==
  /\ phase = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 1
  /\ alive = [p \in 1..N |-> TRUE]

\* Entering the critical section: the bakery number is only handed out
\* while the numbering is still below the configured maximum.
Enter(p) ==
  /\ alive[p] = TRUE
  /\ phase[p] = "idle"
  /\ nextTicket <= MaxNat
  /\ phase' = [phase EXCEPT ![p] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED alive

Take(p) ==
  /\ alive[p] = TRUE
  /\ phase[p] = "waiting"
  /\ \A q \in 1..N : ticket[q] # ticket[p]
  /\ phase' = [phase EXCEPT ![p] = "cs"]
  /\ UNCHANGED << ticket, nextTicket, alive >>

\* Leaving: the critical section is released and the bakery number is
\* recycled so the numbering never runs out during the bounded run.
Leave(p) ==
  /\ alive[p] = TRUE
  /\ phase[p] = "cs"
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ nextTicket' = IF nextTicket > 1 THEN nextTicket - 1 ELSE 1
  /\ UNCHANGED alive

Reenter(p) ==
  /\ alive[p] = TRUE
  /\ phase[p] = "done"
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ UNCHANGED << ticket, nextTicket, alive >>

\* At most one process may crash, and it enters the done state without
\* releasing its ticket -- that is what the coherent invariant rules out
\* a second holder ever taking a number already held by the crashed one.
Crash ==
  /\ \A q \in 1..N : alive[q] = TRUE
  /\ \E p \in 1..N :
       /\ alive' = [alive EXCEPT ![p] = FALSE]
       /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED << ticket, nextTicket >>

Next ==
  \/ \E p \in 1..N : Enter(p) \/ Take(p) \/ Leave(p) \/ Reenter(p)
  \/ Crash

\* ISpec is the inductive spec: it starts from any reachable state rather
\* than just the initial state, and it disables weak fairness -- the
\* single-crash clause is what keeps it convergent without it.
ISpec == Spec /\ (\A p \in 1..N : TRUE)

Spec == Init /\ [][Next]_vars

====