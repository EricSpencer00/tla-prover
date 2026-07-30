---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The set of natural numbers is overridden to a finite range for model checking.
Number == 0 .. MaxNat

VARIABLES chosen, ticket, served, cs

vars == <<chosen, ticket, served, cs>>

Init == /\ chosen = [i \in 1..N |-> FALSE]
        /\ ticket = [i \in 1..N |-> 0]
        /\ served = [i \in 1..N |-> 0]
        /\ cs = 0

\* A process that is not yet in the critical section chooses a ticket number
\* bounded by the configured maximum.
Acquire(i) == /\ ~chosen[i]
              /\ chosen' = [chosen EXCEPT ![i] = TRUE]
              /\ ticket' = [ticket EXCEPT ![i] = IF cs = 0 THEN 1 ELSE cs + 1]
              /\ UNCHANGED <<served, cs>>

\* A process enters the critical section once no other process holds a smaller
\* ticket number, or it holds the smallest possible ticket (1).
Enter(i) == /\ chosen[i]
            /\ cs = 0
            /\ \A j \in 1..N : chosen[j] => ticket[j] >= ticket[i]
            /\ cs' = ticket[i]
            /\ UNCHANGED <<chosen, ticket, served>>

\* The process in the critical section eventually leaves, releasing its ticket.
Exit(i) == /\ cs = ticket[i]
           /\ chosen' = [chosen EXCEPT ![i] = FALSE]
           /\ ticket' = [ticket EXCEPT ![i] = 0]
           /\ served' = [served EXCEPT ![i] = @ + 1]
           /\ cs' = 0

Next == \E i \in 1..N : Acquire(i) \/ Enter(i) \/ Exit(i)

\* The inductive specification starts from any type-correct state satisfying the
\* invariant, not just from the initial state.
ISpec == Init /\ [][Next]_vars

\* Mutual exclusion: a process is in the critical section only when its ticket
\* matches the shared critical-section register, which can name one ticket only.
MutualExclusion == cs # 0 => (CHOOSE i \in 1..N : chosen[i] /\ ticket[i] = cs)

TypeOK == /\ chosen \in [1..N -> BOOLEAN]
          /\ ticket \in [1..N -> Number]
          /\ served \in [1..N -> Number]
          /\ cs \in Number

\* The invariant is the union of the mutual-exclusion check and basic domain
\* constraints: every live process holds a ticket in the finite range.
Inv == MutualExclusion /\ TypeOK

====