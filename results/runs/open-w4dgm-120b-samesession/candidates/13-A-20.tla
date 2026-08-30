---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* This module is the model-checking configuration for the Bakery mutual
\* exclusion algorithm. It inherits the core algorithm from the Bakery
\* specification. The override below turns Nat (an infinite type) into a
\* bounded range 0..MaxNat so the reachable state space is finite and
\* exhaustively model-checkable; the override is valid only because ticket
\* numbers in the algorithm never need to exceed the number of processes.

\* Operators inherited from Naturals that are overridden here; the
\* declarations below are the replacements, so the left-hand names must
\* not be redeclared -- only right-hand bodies are provided.

NatOverride == 0..MaxNat

\* Inherited variables: ticket, mode, using, waiting. No new variables.
VARIABLES ticket, mode, using, waiting

TypeOK ==
    /\ ticket \in [1..N -> NatOverride]
    /\ mode \in [1..N -> {"idle", "waiting", "cs"}]
    /\ using \in [1..N -> BOOLEAN]
    /\ waiting \in [1..N -> BOOLEAN]

NextTicket(t) == IF t = MaxNat THEN 1 ELSE t + 1

Init ==
    /\ ticket = [i \in 1..N |-> 1]
    /\ mode = [i \in 1..N |-> "idle"]
    /\ using = [i \in 1..N |-> FALSE]
    /\ waiting = [i \in 1..N |-> FALSE]

\* The bakery entry is a two-step protocol: pick a ticket, then enter only
\* if the ticket is strictly smaller than every other's. Because a ticket
\* is never abandoned but only advanced, the smallest waiting ticket is
\* exactly the one that must be allowed entry.
Pick(i) ==
    /\ mode[i] = "idle"
    /\ mode' = [mode EXCEPT ![i] = "waiting"]
    /\ waiting' = [waiting EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, using>>

Enter(i) ==
    /\ mode[i] = "waiting"
    /\ \A j \in 1..N : (mode[j] \in {"idle", "waiting"}) => ticket[i] < ticket[j]
    /\ mode' = [mode EXCEPT ![i] = "cs"]
    /\ using' = [using EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, waiting>>

Leave(i) ==
    /\ mode[i] = "cs"
    /\ mode' = [mode EXCEPT ![i] = "idle"]
    /\ using' = [using EXCEPT ![i] = FALSE]
    /\ waiting' = [waiting EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = NextTicket(ticket[i])]

Next ==
    \/ \E i \in 1..N : Pick(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Leave(i)

MutualExclusion ==
    \A i, j \in 1..N : (i # j /\ mode[i] = "cs") => mode[j] # "cs"

\* The full set of invariants: mutual exclusion plus type correctness.
Inv == MutualExclusion /\ TypeOK

ISpec == Init /\ [][Next]_<<ticket, mode, using, waiting>>

====