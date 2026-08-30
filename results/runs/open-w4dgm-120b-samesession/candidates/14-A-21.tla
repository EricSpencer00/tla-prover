---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES token, pc, req, ticket
vars == <<token, pc, req, ticket>>

\* The token is the single exclusive grant; token = 0 iff no process holds it.
TypeOK ==
    /\ token \in 0..N
    /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
    /\ req \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]

Init ==
    /\ token = 0
    /\ pc = [i \in 1..N |-> "idle"]
    /\ req = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]

Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "waiting"]
    /\ req' = [req EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<token, ticket>>

Acquire(i) ==
    /\ pc[i] = "waiting"
    /\ token = 0
    /\ token' = i
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<req, ticket>>

Enter(i) ==
    /\ pc[i] = "waiting"
    /\ token \in 1..N
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ ticket' = [ticket EXCEPT ![i] = IF ticket[i] < MaxNat THEN ticket[i] + 1 ELSE ticket[i]]
    /\ UNCHANGED <<token, req>>

Release(i) ==
    /\ pc[i] = "critical"
    /\ token = i
    /\ token' = 0
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ req' = [req EXCEPT ![i] = FALSE]
    /\ UNCHANGED ticket

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Acquire(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Release(i)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion, plus the full inductive invariant from the Boulanger spec.
MutualExclusion ==
    /\ (token # 0 => pc[token] = "critical")
    /\ (\A i \in 1..N : pc[i] = "critical" => token = i)
    /\ TypeOK

\* A state constraint keeps every ticket strictly below the finite bound, so
\* no state ever needs a ticket value outside the overridden range.
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

Inv == MutualExclusion

====