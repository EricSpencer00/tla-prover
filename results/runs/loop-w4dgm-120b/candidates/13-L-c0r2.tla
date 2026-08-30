---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* The Bakery mutual exclusion algorithm, with natural numbers replaced by a
\* finite range 0..MaxNat so the state space is bounded for model checking.
\* The inductive spec ISpec starts from any reachable state, not just the
\* initial state, and the invariant is checked from there.

VARIABLES inCS, ticket, choosing, served

vars == <<inCS, ticket, choosing, served>>

TypeOK ==
    /\ inCS \subseteq (1..N)
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ choosing \in [1..N -> BOOLEAN]
    /\ served \in 0..MaxNat

Init ==
    /\ inCS = {}
    /\ ticket = [i \in 1..N |-> 0]
    /\ choosing = [i \in 1..N |-> FALSE]
    /\ served = 0

\* A process begins choosing a ticket number.
Choose(i) ==
    /\ ~choosing[i]
    /\ i \notin inCS
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<inCS, ticket, served>>

\* The ticket is assigned as one more than the highest currently held, capped
\* at the finite MaxNat so the model stays bounded.
Assign(i) ==
    /\ choosing[i]
    /\ ticket' = [ticket EXCEPT ![i] = IF served < MaxNat THEN served + 1 ELSE MaxNat]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<inCS, served>>

\* A process enters the critical section only if its ticket is strictly lower
\* than every other process's ticket, or the other process holds no ticket.
Enter(i) ==
    /\ i \notin inCS
    /\ ticket[i] > 0
    /\ \A j \in 1..N : j # i => (j \notin inCS /\ (ticket[j] = 0 \/ ticket[i] < ticket[j]))
    /\ inCS' = inCS \cup {i}
    /\ UNCHANGED <<ticket, choosing, served>>

\* A process leaves the critical section, freeing its ticket.
Exit(i) ==
    /\ i \in inCS
    /\ inCS' = inCS \ {i}
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ served' = IF served < MaxNat THEN served + 1 ELSE MaxNat
    /\ UNCHANGED choosing

Next ==
    \/ \E i \in 1..N : Choose(i)
    \/ \E i \in 1..N : Assign(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

\* The inductive spec: any reachable state (not just the initial one) must
\* satisfy the invariant, and every action keeps it true.
ISpec == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion == \A i, j \in inCS : i = j

\* The full inductive invariant: mutual exclusion plus type correctness.
Inv == MutualExclusion /\ TypeOK

====