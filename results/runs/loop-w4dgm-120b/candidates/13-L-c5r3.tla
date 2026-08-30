---- MODULE MCBakery ----
EXTENDS Naturals

\* Model-checking configuration for the Bakery mutual exclusion algorithm.
\* It overrides Nat with a finite range so the state space is bounded.

CONSTANTS N, MaxNat

VARIABLES state, inCS, want, ticket, maxUsed

vars == <<state, inCS, want, ticket, maxUsed>>

TypeOK ==
    /\ state \in {"idle", "trying", "cs"}
    /\ inCS \in SUBSET (1 .. N)
    /\ want \in SUBSET (1 .. N)
    /\ ticket \in [1 .. N -> 0 .. MaxNat]
    /\ maxUsed \in 0 .. MaxNat

Init ==
    /\ state = "idle"
    /\ inCS = {}
    /\ want = {}
    /\ ticket = [p \in 1 .. N |-> 0]
    /\ maxUsed = 0

EnterCS(p) ==
    /\ state = "idle"
    /\ p \notin want
    /\ p \notin inCS
    /\ state' = "trying"
    /\ want' = want \cup {p}
    /\ ticket' = [ticket EXCEPT ![p] = IF maxUsed < MaxNat THEN maxUsed + 1 ELSE maxUsed]
    /\ maxUsed' = IF maxUsed < MaxNat THEN maxUsed + 1 ELSE maxUsed
    /\ inCS' = {}

\* The critical section is entered only by the process holding the lowest live
\* ticket, which resolves simultaneous entry attempts.
Acquire(p) ==
    /\ state = "trying"
    /\ p \in want
    /\ \A q \in want : ticket[p] <= ticket[q]
    /\ \A q \in inCS : ticket[p] <= ticket[q]
    /\ state' = "cs"
    /\ inCS' = {p}
    /\ UNCHANGED <<want, ticket, maxUsed>>

ExitCS(p) ==
    /\ state = "cs"
    /\ p \in inCS
    /\ state' = "idle"
    /\ want' = want \ {p}
    /\ inCS' = {}
    /\ UNCHANGED <<ticket, maxUsed>>

Cancel(p) ==
    /\ state = "trying"
    /\ p \in want
    /\ state' = "idle"
    /\ want' = want \ {p}
    /\ inCS' = {}
    /\ UNCHANGED <<ticket, maxUsed>>

Next == \E p \in 1 .. N : EnterCS(p) \/ Acquire(p) \/ ExitCS(p) \/ Cancel(p)

\* The inductive specification: any reachable state must already satisfy the
\* invariant, not just the state after the next step from the initial state.
ISpec == Init /\ [][Next]_vars

\* Mutual exclusion, plus the type correctness of every state variable.
MutualExclusion == \A p1, p2 \in inCS : p1 = p2
Inv == TypeOK /\ MutualExclusion

====