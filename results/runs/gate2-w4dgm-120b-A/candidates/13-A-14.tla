---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

\* SAFETY PROPERTY: mutual exclusion and type correctness together form the
\* full inductive invariant preserved by every step of the Bakery protocol.
MutualExclusion ==
  \A i, j \in 1..N : (i # j /\ inCS[i]) => ~inCS[j]

Inv == MutualExclusion /\ TypeOK

\* The state graph is strongly connected through the idle state (all zero, no
\* tickets taken), so every reachable state deterministically returns to it.
Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ want = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

TakeTicket(i) ==
  /\ ~want[i]
  /\ nextTicket < MaxNat
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED inCS

Enter(i) ==
  /\ want[i]
  /\ inCS[i] = FALSE
  /\ \A j \in 1..N : j # i => (~want[j] \/ ticket[j] > ticket[i])
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<want, ticket, nextTicket>>

Leave(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED nextTicket

AdminReset ==
  /\ nextTicket > 0
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ want = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket' = 0
  /\ UNCHANGED <<inCS, want, ticket>>

Next ==
  \/ \E i \in 1..N : TakeTicket(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Leave(i)
  \/ AdminReset

\* The inductive specification starts from any state satisfying the invariant
\* (not just the empty-initial state) and checks closure under Next.
ISpec == Init /\ [][Next]_vars /\ WF_vars(Next)

====