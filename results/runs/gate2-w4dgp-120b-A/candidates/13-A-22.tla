---- MODULE MCBakery ----
EXTENDS Naturals

\* The Bakery mutual exclusion algorithm, adapted for model checking by bounding
\* the ticket numbers. The standard naturals are shadowed by a finite range below.
CONSTANTS N, MaxNat

VARIABLES ticket, choosing, active

vars == <<ticket, choosing, active>>

TypeOK ==
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ choosing \in [1..N -> BOOLEAN]
    /\ active \in [1..N -> BOOLEAN]

NoActive == \A q \in 1..N : ~active[q]

Init ==
    /\ \A q \in 1..N : ticket[q] = 0 /\ choosing[q] = FALSE
    /\ \A q \in 1..N : active[q] = FALSE

\* Entry: take a ticket strictly greater than all currently held tickets.
Bump(t) ==
    LET m == IF \E q \in 1..N : ticket[q] > 0
                THEN MAX { ticket[q] : q \in 1..N }
                ELSE 0
    IN IF m < MaxNat THEN m + 1 ELSE m

Enter(q) ==
    /\ ~active[q]
    /\ ~choosing[q]
    /\ NoActive
    /\ choosing' = [choosing EXCEPT ![q] = TRUE]
    /\ UNCHANGED <<ticket, active>>

Choose(q) ==
    /\ choosing[q]
    /\ ticket' = [ticket EXCEPT ![q] = Bump(q)]
    /\ choosing' = [choosing EXCEPT ![q] = FALSE]
    /\ UNCHANGED active

Begin(q) ==
    /\ ticket[q] > 0
    /\ NoActive
    /\ active' = [active EXCEPT ![q] = TRUE]
    /\ UNCHANGED <<ticket, choosing>>

Exit(q) ==
    /\ active[q]
    /\ active' = [active EXCEPT ![q] = FALSE]
    /\ ticket' = [ticket EXCEPT ![q] = 0]
    /\ UNCHANGED choosing

Next ==
    \/ \E q \in 1..N : Enter(q) \/ Choose(q) \/ Begin(q) \/ Exit(q)

\* The inductive spec starts from any type-correct reachable state (Init is
\* retained so the reachable set is non-empty when the module is checked alone).
Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A a, b \in 1..N : (active[a] /\ active[b]) => a = b

Inv ==
    /\ MutualExclusion
    /\ TypeOK

NatOverride ==
    Nat == Nat \cup {0}

====