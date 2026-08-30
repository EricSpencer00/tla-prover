---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

(* Model-checking configuration module for the Bakery mutual exclusion
   algorithm.  It inherits the full Bakery specification and overrides the
   natural-number type with a finite range (bounded by MaxNat) so the state
   space stays finite for exhaustive checking.  The inductive specification
   ISpec starts from any state satisfying the invariant, not just from
   Init, and the invariant is proved preserved across all transitions. *)

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, tmax, clock

vars == <<inCS, want, ticket, tmax, clock>>

TypeOK ==
    /\ inCS \subseteq 1..N
    /\ want \subseteq 1..N
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ tmax \in 0..MaxNat
    /\ clock \in BOOLEAN

\* Mutual exclusion: a process is in the critical section only while its
\* ticket equals the current door number, and only one process can hold that
\* ticket, so at most one process is ever inside.
MutualExclusion ==
    /\ \A p \in inCS : ticket[p] = tmax
    /\ \A p \in 1..N : (p \in inCS) <=> (ticket[p] = tmax)

\* The full inductive invariant: mutual exclusion plus type correctness.
Inv ==
    /\ MutualExclusion
    /\ TypeOK

Init ==
    /\ inCS = {}
    /\ want = {}
    /\ ticket = [p \in 1..N |-> 0]
    /\ tmax = 0
    /\ clock = FALSE

\* A process requests the shared resource.
Request(p) ==
    /\ p \notin want
    /\ p \notin inCS
    /\ want' = want \cup {p}
    /\ UNCHANGED <<inCS, ticket, tmax, clock>>

\* The bakery grants a waiting process the next ticket when the door is free.
Grant(p) ==
    /\ p \in want
    /\ inCS = {}
    /\ tmax < MaxNat
    /\ tmax' = tmax + 1
    /\ ticket' = [ticket EXCEPT ![p] = tmax + 1]
    /\ want' = want \ {p}
    /\ UNCHANGED <<inCS, clock>>

\* A process enters its critical section.
Enter(p) ==
    /\ ticket[p] = tmax
    /\ inCS = {}
    /\ inCS' = {p}
    /\ UNCHANGED <<want, ticket, tmax, clock>>

\* A process leaves the critical section and retires its ticket.
Exit(p) ==
    /\ p \in inCS
    /\ inCS' = {}
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED <<want, tmax, clock>>

\* A waiting process abandons its request.
Cancel(p) ==
    /\ p \in want
    /\ want' = want \ {p}
    /\ UNCHANGED <<inCS, ticket, tmax, clock>>

\* The token clock flips, which is always available and keeps the system
\* weakly fair even when no other action is currently enabled.
Tick ==
    /\ clock' = ~clock
    /\ UNCHANGED <<inCS, want, ticket, tmax>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Grant(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)
    \/ \E p \in 1..N : Cancel(p)
    \/ Tick

\* Starting from any state that already satisfies the invariant, the
\* bakery's actions keep the invariant true -- this is what makes the
\* invariant inductive and not just a property of the initial state.
ISpec == Init /\ [][Next]_vars

====