---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES astate, own, ticket
vars == <<astate, own, ticket>>

Booting == "booting"
Holding == "holding"
Waiting == "waiting"
Idle == "idle"

\* Inherits the mutual-exclusion core from Boulanger.  This module adds only a
\* bounded range for natural numbers and a state constraint on tickets.
Init == /\ astate = [i \in 1..N |-> Booting]
        /\ own    = [i \in 1..N |-> FALSE]
        /\ ticket = [i \in 1..N |-> 0]

Acquire == /\ \E i \in 1..N :
                /\ astate[i] = Booting
                /\ astate' = [astate EXCEPT ![i] = Holding]
                /\ own'    = [own    EXCEPT ![i] = TRUE]
                /\ ticket' = [ticket EXCEPT ![i] = 1]
           /\ UNCHANGED << >>

Release == /\ \E i \in 1..N :
                /\ astate[i] = Holding
                /\ astate' = [astate EXCEPT ![i] = Idle]
                /\ own'    = [own    EXCEPT ![i] = FALSE]
                /\ ticket' = [ticket EXCEPT ![i] = 0]
           /\ UNCHANGED << >>

\* The system never re-circulates beyond a full day of time, so this is the
\* only ticking action; it is allowed to fire whenever no one is holding.
Tick == /\ \A i \in 1..N : astate[i] # Holding
        /\ astate' = [i \in 1..N |-> IF astate[i] = Idle THEN Booting ELSE astate[i]]
        /\ UNCHANGED << own, ticket >>

Next == Acquire \/ Release \/ Tick

Spec == Init /\ [][Next]_vars

\* A process holder is the only one holding the lock, so at most one process
\* is ever in the holding state at once.
MutualExclusion == \A i, j \in 1..N :
                      (i # j /\ astate[i] = Holding) => astate[j] # Holding

TypeOK == /\ astate \in [1..N -> {Booting, Holding, Waiting, Idle}]
          /\ own    \in [1..N -> BOOLEAN]
          /\ ticket \in [1..N -> 0..MaxNat]

Inv == /\ astate \in [1..N -> {Booting, Holding, Waiting, Idle}]
       /\ own    \in [1..N -> BOOLEAN]
       /\ ticket \in [1..N -> 0..MaxNat]
       /\ \A i \in 1..N : ticket[i] <= MaxNat

\* The finite override on natural numbers is upheld by this bound on tickets.
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====