---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

(* Finite-number model-checking wrapper around the Boulanger mutual exclusion *)
(* algorithm.  Private tickets live in a bounded range and a state constraint  *)
(* prunes states where they would overflow that range.                        *)

CONSTANTS N, MaxNat

VARIABLES inCS, ticket, served, active, inSystem

vars == <<inCS, ticket, served, active, inSystem>>

Range(f) == { f[i] : i \in 1..N }

TypeOK ==
    /\ inCS \in BOOLEAN
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ served \in 0..MaxNat
    /\ active \subseteq 1..N
    /\ inSystem \subseteq 1..N

Init ==
    /\ inCS = FALSE
    /\ ticket = [i \in 1..N |-> 0]
    /\ served = 0
    /\ active = 1..N
    /\ inSystem = {}

TakeTicket(i) ==
    /\ i \in active
    /\ i \notin inSystem
    /\ inCS = FALSE
    /\ inSystem' = inSystem \cup {i}
    /\ ticket' = [ticket EXCEPT ![i] = served]
    /\ UNCHANGED <<inCS, served, active>>

Enter(i) ==
    /\ i \in inSystem
    /\ inCS = FALSE
    /\ inCS' = TRUE
    /\ served' = served + 1
    /\ UNCHANGED <<ticket, active, inSystem>>

Leave(i) ==
    /\ inCS = TRUE
    /\ inSystem' = inSystem \ {i}
    /\ inCS' = FALSE
    /\ UNCHANGED <<ticket, served, active>>

Retire(i) ==
    /\ i \in active
    /\ i \notin inSystem
    /\ active' = active \ {i}
    /\ UNCHANGED <<inCS, ticket, served, inSystem>>

Rejoin(i) ==
    /\ i \notin active
    /\ active' = active \cup {i}
    /\ UNCHANGED <<inCS, ticket, served, inSystem>>

Next ==
    \/ \E i \in 1..N : TakeTicket(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Leave(i)
    \/ \E i \in 1..N : Retire(i)
    \/ \E i \in 1..N : Rejoin(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i \in 1..N : i \in inSystem => inCS

Inv ==
    /\ \A i \in 1..N : (i \in inSystem) <=> (ticket[i] \in Range(ticket))
    /\ \A i \in 1..N : (i \in inSystem) => (i \in active)
    /\ \A i, j \in 1..N :
        (i \in inSystem /\ j \in inSystem /\ ticket[i] = ticket[j]) => i = j

FiniteNatBound ==
    \A i \in 1..N : ticket[i] < MaxNat

====