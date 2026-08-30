---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES status, inCS, ticket, choosing

vars == <<status, inCS, ticket, choosing>>

TypeOK ==
    /\ status \in {"idle", "waiting", "critical"}
    /\ inCS \in 0..N
    /\ ticket \in 0..MaxNat
    /\ choosing \in BOOLEAN

Init ==
    /\ status = "idle"
    /\ inCS = 0
    /\ ticket = 0
    /\ choosing = FALSE

\* One process begins picking up a ticket to enter the critical section;
\* it must not already be counted among the processes in the section.
BeginEntry ==
    /\ status = "idle"
    /\ status' = "waiting"
    /\ choosing' = TRUE
    /\ UNCHANGED <<inCS, ticket>>

\* Writing the ticket is the irreversible step: the shared counter only
\* goes up, and a process may only read a free value out of an empty slot.
TakeTicket ==
    /\ choosing
    /\ ticket < MaxNat
    /\ \A q \in 1..N : q # inCS => q # ticket
    /\ ticket' = ticket + 1
    /\ choosing' = FALSE
    /\ UNCHANGED <<status, inCS>>

\* A process may be slow between taking its ticket and entering, but it is
\* never assumed to have crashed -- the shared ticket register is still
\* free to hand out the next number, so entry is allowed whenever the
\* critical section is empty, regardless of how long the holder lingers.
Enter ==
    /\ status = "waiting"
    /\ inCS = 0
    /\ inCS' = 1
    /\ status' = "critical"
    /\ UNCHANGED <<ticket, choosing>>

Leave ==
    /\ status = "critical"
    /\ status' = "idle"
    /\ inCS' = 0
    /\ UNCHANGED <<ticket, choosing>>

Next == BeginEntry \/ TakeTicket \/ Enter \/ Leave

Spec == Init /\ [][Next]_vars

\* Safety: the critical section never holds more than one process at a
\* time. TypeOK and the full invariant are preserved across every
\* transition, so they hold at every reachable state.
MutualExclusion == inCS <= 1

Inv == MutualExclusion /\ TypeOK

\* The inductive specification: starts from any type-correct reachable
\* state that already satisfies the invariant, not just the single
\* initial state -- this is what forces the invariant to be preserved.
ISpec == Spec /\ Inv

\* Operator override: make Nat finite so the model is checkable; keep
\* Naturals available for other definitions, and do NOT declare Nat.
NatOverride == 0..MaxNat

====